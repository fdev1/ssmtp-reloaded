/*

 sSMTP -- send messages via SMTP to a mailhub for local delivery or forwarding.
 This program is used in place of /usr/sbin/sendmail, called by "mail" (et all).
 sSMTP does a selected subset of sendmail's standard tasks (including exactly
 one rewriting task), and explains if you ask it to do something it can't. It
 then sends the mail to the mailhub via an SMTP connection. Believe it or not,
 this is nothing but a filter

 See COPYRIGHT for the license

*/
#define VERSION "0.9"
#define _GNU_SOURCE

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/param.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <syslog.h>
#include <signal.h>
#include <setjmp.h>
#include <string.h>
#include <ctype.h>
#include <netdb.h>
#ifdef HAVE_SSL
#ifdef HAVE_GNUTLS
#include <gnutls/openssl.h>
#else
#include <openssl/crypto.h>
#include <openssl/x509.h>
#include <openssl/pem.h>
#include <openssl/ssl.h>
#include <openssl/err.h>
#endif
#endif
#ifdef MD5AUTH
#include "md5auth/hmac_md5.h"
#endif
#include "ssmtp.h"
#include <fcntl.h>
#include "xgethostname.h"
#include <dirent.h>
#include <langinfo.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <paths.h>
#include <errno.h>

bool_t have_date = False;
bool_t have_from = False;
#ifdef HASTO_OPTION
bool_t have_to = False;
#endif
bool_t minus_t = False;
bool_t minus_v = False;
bool_t override_from = False;
bool_t rewrite_domain = False;
bool_t use_tls = False;			/* Use SSL to transfer mail to HUB */
bool_t use_starttls = False;		/* SSL only after STARTTLS (RFC2487) */
bool_t use_cert = False;		/* Use a certificate to transfer SSL mail */
bool_t use_oldauth = False;		/* use old AUTH LOGIN username style */
bool_t do_not_queue = False;		/* set to true when sending from queue */
bool_t sending = False;			/* Indicates that we're already transmitting */

#define ARPADATE_LENGTH 32		/* Current date in RFC format */
char arpadate[ARPADATE_LENGTH];
char *auth_user = (char*)NULL;
char *auth_pass = (char*)NULL;
char *auth_askpass = (char*)NULL;
char *auth_method = (char*)NULL;	/* Mechanism for SMTP authentication */
char *mail_domain = (char*)NULL;
char *from = (char*)NULL;		/* Use this as the From: address */
char *hostname = (char*)NULL;;
char *mailhost = (char*)NULL;
char *minus_f = (char*)NULL;
char *minus_F = (char*)NULL;
char *gecos = (char*)NULL;;
char *prog = (char*)NULL;
char *root = NULL;
char *tls_cert = "/etc/ssl/certs/ssmtp.pem";	/* Default Certificate */
char *uad = (char*)NULL;
char *config_file = (char*)NULL;		/* alternate configuration file */
char *queue_dir = (char*)NULL;
char *comm_error = (char*)NULL;

headers_t headers, *ht;

#ifdef DEBUG
int log_level = 1;
#else
int log_level = 0;
#endif
int minuserid = MAXSYSUID+1;
int port = 25;
#ifdef INET6
int p_family = PF_UNSPEC;		/* Protocol family used in SMTP connection */
#endif

jmp_buf TimeoutJmpBuf;			/* Timeout waiting for input from network */

rcpt_t rcpt_list, *rt;
char **rcptv = (char**) NULL;

#ifdef HAVE_SSL
SSL *ssl;
#endif

#ifdef MD5AUTH
static char hextab[]="0123456789abcdef";
#endif

ssize_t outbytes;

char *addr_parse(char *str);
char *rcpt_remap(char *str);
int main(int argc, char **argv);

/*
log_event() -- Write event to syslog (or log file if defined)
*/
void log_event(int priority, char *format, ...)
{
	char buf[(BUF_SZ + 1)];
	va_list ap;

	va_start(ap, format);
	(void)vsnprintf(buf, BUF_SZ, format, ap);
	va_end(ap);

#ifdef LOGFILE
	FILE *fp;

	if((fp = fopen("/tmp/ssmtp.log", "a")) != (FILE *)NULL) {
		(void)fprintf(fp, "%s\n", buf);
		(void)fclose(fp);
	}
	else {
		(void)fprintf(stderr, "Can't write to /tmp/ssmtp.log\n");
	}
#endif

#if HAVE_SYSLOG_H
#if OLDSYSLOG
	openlog("sSMTP-Reloaded", LOG_PID);
#else
	openlog("sSMTP-Reloaded", LOG_PID, LOG_MAIL);
#endif
	syslog(priority, "%s", buf);
	closelog();
#endif
}

ssize_t smtp_write(int fd, char *format, ...);
int smtp_read(int fd, char *response);
int smtp_read_all(int fd, char *response);
int smtp_okay(int fd, char *response);

/*
gettmpdir() -- gets the temp directory
*/
const char *gettmpdir(void)
{
	char *tmp = NULL;
	if(getuid() == geteuid() || getgid() == getegid()) {
		tmp = getenv("TMPDIR");
	}
	#if defined(P_tmpdir)
	if(!tmp) {
		tmp = P_tmpdir;
	}
	#endif
	if(!tmp) {
		tmp = _PATH_TMP;
	}
	if(!tmp) {
		tmp = "/tmp";
	}
	return tmp;
}

/*
dead_letter() -- Save stdin to ~/dead.letter if possible
*/
void dead_letter(void)
{
	char *path;
	char buf[(BUF_SZ + 1)];
	struct passwd *pw;
	uid_t uid;
	FILE *fp;

	uid = getuid();
	pw = getpwuid(uid);

	if(isatty(fileno(stdin))) {
		if(log_level > 0) {
			log_event(LOG_ERR,
				"stdin is a TTY - not saving to %s/dead.letter", pw->pw_dir);
		}
		return;
	}

	if(pw == (struct passwd *)NULL) {
		/* Far to early to save things */
		if(log_level > 0) {
			log_event(LOG_ERR, "No sender failing horribly!");
		}
		return;
	}

#define DEAD_LETTER "/dead.letter"
	path = malloc (strlen (pw->pw_dir) + sizeof (DEAD_LETTER));
	if (!path) {
		/* Can't use die() here since dead_letter() is called from die() */
		exit(1);
	}
	memcpy (path, pw->pw_dir, strlen (pw->pw_dir));
	memcpy (path + strlen (pw->pw_dir), DEAD_LETTER, sizeof (DEAD_LETTER));
	
	if((fp = fopen(path, "a")) == (FILE *)NULL) {
		/* Perhaps the person doesn't have a homedir... */
		if(log_level > 0) {
			log_event(LOG_ERR, "Can't open %s failing horribly!", path);
		}
		free(path);
		return;
	}

	/* We start on a new line with a blank line separating messages */
	(void)fprintf(fp, "\n\n");

	while(fgets(buf, sizeof(buf), stdin)) {
		(void)fputs(buf, fp);
	}

	if(fclose(fp) == -1) {
		if(log_level > 0) {
			log_event(LOG_ERR,
				"Can't close %s/dead.letter, possibly truncated", pw->pw_dir);
		}
	}
	free(path);
}

/*
genmailid() -- generates an email id
*/
const char *genmailid(void)
{
	int i, j;
	static char mailid[13];
	char charset[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
	for(i = 0; i < 12; i++) {
		j = (int) ((double) rand() / RAND_MAX * (sizeof(charset) - 1));
		mailid[i] = charset[j];
	}
	mailid[12] = '\0';
	return mailid;
}

/*
queue_message() -- save message to queue directory
*/
bool_t queue_message(const char *err)
{
	int fd, i;
	const char *delim = "sSMTP:";
	const char *temp;
	char *p, *q, *template, buf[64];
	if(isatty(fileno(stdin))) {
		if(log_level > 0) {
			log_event(LOG_ERR, "Message not queued: STDIN is a TTY");
		}
		fprintf(stderr, "%s: Message not queued: STDIN is a TTY\n", prog);
		return False;
	}
	temp = gettmpdir();
	template = malloc(strlen(temp) + (13 * sizeof(char)));
	if(!template) {
		if(log_level > 0) {
			log_event(LOG_ERR, "Could not queue message: out of memory");
		}
		fprintf(stderr, "%s: Could not queue message: out of memory\n", prog);
		return False;
	}
	strcpy(template, temp);
	strcat(template, "/mail-XXXXXX");
	if((fd = mkstemp(template)) == -1) {
		if(log_level > 0) {
			log_event(LOG_ERR, "Could not queue message: mkstemp(\"%s\") failed", template);
		}
		fprintf(stderr, "%s: Could not queue message: mkstemp(\"%s\") failed\n", prog, template);
		free(template);
		return False;
	}
	if(minus_t) {
		if(write(fd, delim, strlen(delim)) == -1 ||
			write(fd, "-t", 2) == -1) {
			goto write_failed;
		}
	}
	else {
		for (i = 1; rcptv[i] != NULL; i++) {
			p = strtok(rcptv[i], ",");
			while(p) {
				if((p = addr_parse(p)) == NULL) {
					fprintf(stderr, "%s: Could not queue message: Out of memory\n", prog);
					close(fd);
					remove(template);
					free(template);
					return False;
				}
				if((q = rcpt_remap(p)) == NULL) {
					fprintf(stderr, "%s: Could not queue message: Out of memory\n", prog);
					close(fd);
					remove(template);
					free(template);
					free(p);
					return False;
				}
				free(p);
				if(write(fd, delim, strlen(delim)) == -1 ||
					write(fd, q, strlen(q)) == -1) {
					free(q);
					goto write_failed;
				}
				free(q);
				delim = ",";
				p = strtok(NULL, ",");
			}
		}
	}
	if(comm_error) {
		char *source = "127.0.0.1";
		if(sending) {
			source = mailhost;
		}
		if(write(fd, "|(host ", sizeof(char) * 7) == -1 ||
			write(fd, source, strlen(source)) == -1 ||
			write(fd, " said: ", sizeof(char) * 7) == -1 ||
			write(fd, comm_error, strlen(comm_error)) == -1 ||
			write(fd, ")", sizeof(char)) == -1) {
			goto write_failed;
		}
	}
	else if (err) {
		if(write(fd, "|", sizeof(char)) == -1 ||
			write(fd, err, strlen(err)) == -1) {
			goto write_failed;
		}
	}

	ht = &headers;
	while(ht->next) {
		if(write(fd, "\n", sizeof(char)) == -1 ||
			write(fd, ht->string, strlen(ht->string)) == -1) {
			goto write_failed;
		}
		ht = ht->next;
	}
	if(write(fd, "\n", sizeof(char)) == -1) {
		goto write_failed;
	}
	while (fgets(buf, 64, stdin) != NULL) {
		if(write(fd, buf, strlen(buf)) == -1) {
			goto write_failed;
		}
	}
	close(fd);
	if(chdir(queue_dir) == -1) {
		fprintf(stderr, "%s: Could not access queue directory: %s",
			prog, queue_dir);
		remove(template);
		free(template);
		return False;
	}
	temp = genmailid();
	while(link(template, temp) == -1) {
		if(errno != EEXIST) {
			log_event(LOG_ERR, "Could not queue message: link() failed errno=%i",
				errno);
			fprintf(stderr, "%s: Could not queue message: link failed\n", prog);
			remove(template);
			free(template);
			return False;
		}
		temp = genmailid();
	}
	i = chmod(temp, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP);
	unlink(template);
	free(template);
	return True;

write_failed:
	log_event(LOG_ERR, "Could not queue message: write() failed");
	fprintf(stderr, "%s: Could not queue message: write() failed", prog);
	close(fd);
	remove(template);
	free(template);
	return False;
}

/*
debug_print() -- Print debug message to stderr
*/
void debug_print(char *format, ...) 
{
	if(minus_v) {
		va_list ap;
		va_start(ap, format);
		vfprintf(stderr, format, ap);
		va_end(ap);
	}
}

/*
die() -- Write error message, dead.letter or queue and exit
*/
void __attribute__((noreturn)) die(char *format, ...)
{
	char buf[(BUF_SZ + 1)];
	va_list ap;

	va_start(ap, format);
	vsnprintf(buf, BUF_SZ, format, ap);
	va_end(ap);

	fprintf(stderr, "%s: %s\n", prog, buf);
	log_event(LOG_ERR, "%s", buf);

	if(queue_dir != (char *)NULL) {
		/* if we're sending from queue do not requeue */
		if(do_not_queue)
			exit(1);
		/* Enqueue message for sending later */
		if(queue_message(buf)) {
			fprintf(stderr, "%s: Message queued\n", prog);
			exit(0);
		}
		else {
			fprintf(stderr, "%s: Could not queue message\n", prog);
		}
	}
	else {
		/* Send message to dead.letter */
		dead_letter();
	}
	exit(1);
}

/*
xbasename() -- Return last element of path
*/
char *xbasename(char *str)
{
	char *p;

	p = strrchr(str, '/');
	if (!p) {
		p = str;
	}

	return(strdup(p));
}

/*
strip_pre_ws() -- Return pointer to first non-whitespace character
*/
char *strip_pre_ws(char *str)
{
	char *p;

	p = str;
	while(*p && isspace(*p)) p++;

	return(p);
}

/*
strip_post_ws() -- Return pointer to last non-whitespace character
*/
char *strip_post_ws(char *str)
{
	char *p;

	p = (str + strlen(str));
	while(isspace(*--p)) {
		*p = '\0';
	}

	return(p);
}

/*
addr_parse() -- Parse <user@domain.com> from full email address
*/
char *addr_parse(char *str)
{
	char *p, *q, *s;

#if 0
	(void)fprintf(stderr, "*** addr_parse(): str = [%s]\n", str);
#endif

	/* Simple case with email address enclosed in <> */
	if((s = p = strdup(str)) == (char *)NULL) {
		die("addr_parse(): strdup()");
	}

	if((q = strchr(p, '<'))) {
		q++;

		if((p = strchr(q, '>'))) {
			*p = '\0';
		}

#if 0
		(void)fprintf(stderr, "*** addr_parse(): q = [%s]\n", q);
#endif

		q = strdup(q);
		free(s);
		return(q);
	}

	q = strip_pre_ws(p);
	if(*q == '(') {
		while((*q++ != ')'));
	}
	p = strip_pre_ws(q);

#if 0
	(void)fprintf(stderr, "*** addr_parse(): p = [%s]\n", p);
#endif

	q = strip_post_ws(p);
	if(*q == ')') {
		while((*--q != '('));
		*q = '\0';
	}
	(void)strip_post_ws(p);

#if 0
	(void)fprintf(stderr, "*** addr_parse(): p = [%s]\n", p);
#endif
	p = strdup(p);
	free(s);
	return(p);
}

/*
append_domain() -- Fix up address with @domain.com
*/
char *append_domain(char *str)
{
	char buf[(BUF_SZ + 1)];

	if(strchr(str, '@') == (char *)NULL) {
		if(snprintf(buf, BUF_SZ, "%s@%s", str,
#ifdef REWRITE_DOMAIN
			rewrite_domain == True ? mail_domain : hostname
#else
			hostname
#endif
														) == -1) {
				die("append_domain() -- snprintf() failed");
		}
		return(strdup(buf));
	}

	return(strdup(str));
}

/*
standardise() -- Trim off '\n's and double leading dots
*/
bool_t standardise(char *str, bool_t *linestart)
{
	char *p;
	bool_t leadingdot = False;

	/* Any line beginning with a dot has an additional dot inserted;
	not just a line consisting solely of a dot. Thus we have to move
	the buffer start up one */

	if(*linestart && *str == '.') {
		leadingdot = True;
	}
	*linestart = False;

	if((p = strchr(str, '\n'))) {
		*p = '\0';
		*linestart = True;
	}
	return(leadingdot);
}

/*
revaliases() -- Parse the reverse alias file
	Fix globals to use any entry for sender
*/
void revaliases(struct passwd *pw)
{
	char buf[(BUF_SZ + 1)], *p;
	FILE *fp;

	/* Try to open the reverse aliases file */
	if((fp = fopen(REVALIASES_FILE, "r"))) {
		/* Search if a reverse alias is defined for the sender */
		while(fgets(buf, sizeof(buf), fp)) {
			/* Make comments invisible */
			if((p = strchr(buf, '#'))) {
				*p = '\0';
			}

			/* Ignore malformed lines and comments */
			if(strchr(buf, ':') == (char *)NULL) {
				continue;
			}

			/* Parse the alias */
			if(((p = strtok(buf, ":"))) && !strcmp(p, pw->pw_name)) {
				if((p = strtok(NULL, ": \t\r\n"))) {
					if(uad) {
						free(uad);
					}
					if((uad = strdup(p)) == (char *)NULL) {
						die("revaliases() -- strdup() failed");
					}
				}

				if((p = strtok(NULL, " \t\r\n:"))) {
					if(mailhost) {
						free(mailhost);
					}
					if((mailhost = strdup(p)) == (char *)NULL) {
						die("revaliases() -- strdup() failed");
					}

					if((p = strtok(NULL, " \t\r\n:"))) {
						port = atoi(p);
					}

					if(log_level > 0) {
						log_event(LOG_INFO, "Set MailHub=\"%s\"\n", mailhost);
						log_event(LOG_INFO,
							"via SMTP Port Number=\"%d\"\n", port);
					}
				}
			}
		}

		fclose(fp);
	}
}

/* 
from_strip() -- Transforms "Name <login@host>" into "login@host" or "login@host (Real name)"
*/
char *from_strip(char *str)
{
	char *p;

#if 0
	(void)fprintf(stderr, "*** from_strip(): str = [%s]\n", str);
#endif

	if(strncmp("From:", str, 5) == 0) {
		str += 5;
	}

	/* Remove the real name if necessary - just send the address */
	if((p = addr_parse(str)) == (char *)NULL) {
		die("from_strip() -- addr_parse() failed");
	}
#if 0
	(void)fprintf(stderr, "*** from_strip(): p = [%s]\n", p);
#endif

	return(strdup(p));
}

/*
from_format() -- Generate standard From: line
*/
char *from_format(char *str, bool_t override_from)
{
	char buf[(BUF_SZ + 1)] = "";

	if(override_from) {
		if(minus_f) {
			str = append_domain(minus_f);
		}

		if(minus_F) {
			if(snprintf(buf,
				BUF_SZ, "\"%s\" <%s>", minus_F, str) == -1) {
				die("from_format() -- snprintf() failed");
			}
		}
		else if(gecos) {
			if(snprintf(buf, BUF_SZ, "\"%s\" <%s>", gecos, str) == -1) {
				die("from_format() -- snprintf() failed");
			}
		}
		else {
			if(snprintf(buf, BUF_SZ, "%s", str) == -1) {
				die("from_format() -- snprintf() failed");
			}
		}
	}
	else {
		if(gecos) {
			if(snprintf(buf, BUF_SZ, "\"%s\" <%s>", gecos, str) == -1) {
				die("from_format() -- snprintf() failed");
			}
		}
		else {
			if(snprintf(buf, BUF_SZ, "%s", str) == -1) {
				die("from_format() -- snprintf() failed");
			}
		}
	}

#if 0
	(void)fprintf(stderr, "*** from_format(): buf = [%s]\n", buf);
#endif

	return(strdup(buf));
}

/*
rcpt_save() -- Store entry into RCPT list
*/
void rcpt_save(char *str)
{
	char *p;

# if 1
	/* Horrible botch for group stuff */
	p = str;
	while(*p) p++;

	if(*--p == ';') {
		return;
	}
#endif

#if 0
	(void)fprintf(stderr, "*** rcpt_save(): str = [%s]\n", str);
#endif

	/* Ignore missing usernames */
	if(*str == '\0') {
		return;
	}

	if((rt->string = strdup(str)) == (char *)NULL) {
		die("rcpt_save() -- strdup() failed");
	}

	rt->next = (rcpt_t *)malloc(sizeof(rcpt_t));
	if(rt->next == (rcpt_t *)NULL) {
		die("rcpt_save() -- malloc() failed");
	}
	rt = rt->next;
	rt->string = NULL;
	rt->next = (rcpt_t *)NULL;
}

/*
rcpt_parse() -- Break To|Cc|Bcc into individual addresses
*/
void rcpt_parse(char *str)
{
	bool_t in_quotes = False, got_addr = False;
	char *p, *q, *r, *s;

#if 0
	(void)fprintf(stderr, "*** rcpt_parse(): str = [%s]\n", str);
#endif

	if((p = strdup(str)) == (char *)NULL) {
		die("rcpt_parse(): strdup() failed");
	}
	q = p;

	/* Replace <CR>, <LF> and <TAB> */
	while(*q) {
		switch(*q) {
			case '\t':
			case '\n':
			case '\r':
					*q = ' ';
		}
		q++;
	}
	q = p;

#if 0
	(void)fprintf(stderr, "*** rcpt_parse(): q = [%s]\n", q);
#endif

	r = q;
	while(*q) {
		if(*q == '"') {
			in_quotes = (in_quotes ? False : True);
		}

		/* End of string? */
		if(*(q + 1) == '\0') {
			got_addr = True;
		}

		/* End of address? */
		if((*q == ',') && (in_quotes == False)) {
			got_addr = True;

			*q = '\0';
		}

		if(got_addr) {
			while(*r && isspace(*r)) r++;
			if((s = addr_parse(r)) == NULL) {
				die("Out of memory on rcpt_parse()");
			}
			rcpt_save(s);
			free(s);
			r = (q + 1);
#if 0
			(void)fprintf(stderr, "*** rcpt_parse(): r = [%s]\n", r);
#endif
			got_addr = False;
		}
		q++;
	}
	free(p);
}

/*
rcpt_free() -- Free the recipients list
*/
void rcpt_free(void)
{
	rt = rcpt_list.next;
	while(rt) {
		rcpt_t *next = rt->next;
		if(rt->string) {
			free(rt->string);
		}
		free(rt);
		rt = next;
	}
	if(rcpt_list.string) {
		free(rcpt_list.string);
	}
	memset(&rcpt_list, 0, sizeof(rcpt_t));
}

#ifdef MD5AUTH
int crammd5(char *challengeb64, char *username, char *password, char *responseb64)
{
	int i;
	/* none of these should be unsigned!
	 * TODO: audit md5auth code */
	unsigned char digest[MD5_DIGEST_LEN];
	unsigned char digascii[MD5_DIGEST_LEN * 2];
	unsigned char challenge[(BUF_SZ + 1)];
	unsigned char response[(BUF_SZ + 1)];
	unsigned char secret[(MD5_BLOCK_LEN + 1)]; 

	memset (secret,0,sizeof(secret));
	memset (challenge,0,sizeof(challenge));
	strncpy ((char*)secret, password, sizeof(secret));	
	if (!challengeb64 || strlen(challengeb64) > sizeof(challenge) * 3 / 4)
		return 0;
	from64tobits((char*)challenge, challengeb64);

	hmac_md5(challenge, strlen((char*)challenge), secret, strlen((char*)secret), digest);

	for (i = 0; i < MD5_DIGEST_LEN; i++) {
		digascii[2 * i] = hextab[digest[i] >> 4];
		digascii[2 * i + 1] = hextab[(digest[i] & 0x0F)];
	}
	digascii[MD5_DIGEST_LEN * 2] = '\0';

	if (sizeof(response) <= strlen(username) + sizeof(digascii))
		return 0;
	
	strncpy ((char*)response, username, sizeof(response) - sizeof(digascii) - 2);
	strcat ((char*)response, " ");
	strcat ((char*)response, (char*)digascii);
	to64frombits(responseb64, (unsigned char*)response, strlen((char*)response));

	return 1;
}
#endif

/*
rcpt_remap() -- Alias systems-level users to the person who
	reads their mail. This is variously the owner of a workstation,
	the sysadmin of a group of stations and the postmaster otherwise.
	We don't just mail stuff off to root on the mailhub :-)
*/
char *rcpt_remap(char *str)
{
	struct passwd *pw;
	if((root==NULL) || strlen(root)==0 || strchr(str, '@') ||
		((pw = getpwnam(str)) == NULL) || (pw->pw_uid >= minuserid)) {
		return(append_domain(str));	/* It's not a local systems-level user */
	}
	else {
		return(append_domain(root));
	}
}

/*
header_save() -- Store entry into header list
*/
void header_save(char *str)
{
	char *p;

#if 0
	(void)fprintf(stderr, "header_save(): str = [%s]\n", str);
#endif

	if((p = strdup(str)) == (char *)NULL) {
		die("header_save() -- strdup() failed");
	}
	ht->string = p;

	if(strncasecmp(ht->string, "From:", 5) == 0) {
#if 1
		/* Hack check for NULL From: line */
		if(*(p + 6) == '\0') {
			return;
		}
#endif

#ifdef REWRITE_DOMAIN
		if(override_from == True) {
			if(uad != NULL) {
				free(uad);
			}
			uad = from_strip(ht->string);
		}
		else {
			return;
		}
#endif
		have_from = True;
	}
#ifdef HASTO_OPTION
	else if(strncasecmp(ht->string, "To:" ,3) == 0) {
		have_to = True;
	}
#endif
	else if(strncasecmp(ht->string, "Date:", 5) == 0) {
		have_date = True;
	}

	if(minus_t) {
		/* Need to figure out recipients from the e-mail */
		if(strncasecmp(ht->string, "To:", 3) == 0) {
			p = (ht->string + 3);
			rcpt_parse(p);
		}
		else if(strncasecmp(ht->string, "Bcc:", 4) == 0) {
			p = (ht->string + 4);
			rcpt_parse(p);
                        /* Undo adding the header to the list: */
                        free(ht->string);
                        ht->string = NULL;
                        return;
		}
		else if(strncasecmp(ht->string, "CC:", 3) == 0) {
			p = (ht->string + 3);
			rcpt_parse(p);
		}
	}

#if 0
	(void)fprintf(stderr, "header_save(): ht->string = [%s]\n", ht->string);
#endif

	ht->next = (headers_t *)malloc(sizeof(headers_t));
	if(ht->next == (headers_t *)NULL) {
		die("header_save() -- malloc() failed");
	}
	ht = ht->next;
	ht->string = NULL;
	ht->next = (headers_t *)NULL;
}

/*
header_parse() -- Break headers into seperate entries
*/
void header_parse(FILE *stream)
{
	size_t size = BUF_SZ, len = 0;
	char *p = (char *)NULL, *q;
	bool_t in_header = True;
	char l = '\0';
	int c;

	while(in_header && ((c = fgetc(stream)) != EOF)) {
		/* Must have space for up to two more characters, since we
			may need to insert a '\r' */
		if((p == (char *)NULL) || (len >= (size - 1))) {
			size += BUF_SZ;

			p = (char *)realloc(p, (size * sizeof(char)));
			if(p == (char *)NULL) {
				die("header_parse() -- realloc() failed");
			}
			q = (p + len);
		}
		len++;

		if(l == '\n') {
			switch(c) {
				case ' ':
				case '\t':
						/* Must insert '\r' before '\n's embedded in header
						   fields otherwise qmail won't accept our mail
						   because a bare '\n' violates some RFC */
						
						*(q - 1) = '\r';	/* Replace previous \n with \r */
						*q++ = '\n';		/* Insert \n */
						len++;
						
						break;

				case '\n':
						in_header = False;

				default:
						*q = '\0';
						if((q = strrchr(p, '\n'))) {
							*q = '\0';
						}
						header_save(p);

						q = p;
						len = 0;
			}
		}
		*q++ = c;

		l = c;
	}
	if(in_header) {
		if(l == '\n') {
			switch(c) {
				case ' ':
				case '\t':
						/* Must insert '\r' before '\n's embedded in header
						   fields otherwise qmail won't accept our mail
						   because a bare '\n' violates some RFC */
						
						*(q - 1) = '\r';	/* Replace previous \n with \r */
						*q++ = '\n';		/* Insert \n */
						len++;
						
						break;

				case '\n':
						in_header = False;

				default:
						*q = '\0';
						if((q = strrchr(p, '\n'))) {
							*q = '\0';
						}
						header_save(p);

						q = p;
						len = 0;
			}
		}
	}
	(void)free(p);
}

/*
headers_free() -- free the headers list
*/
void headers_free(void)
{
	ht = headers.next;
	while(ht) {
		headers_t *next = ht->next;
		if(ht->string) {
			free(ht->string);
		}
		free(ht);
		ht = next;
	}
	if(headers.string) {
		free(headers.string);
	}
	memset(&headers, 0, sizeof(headers_t));
}

/*
 * This is much like strtok, but does not modify the string
 * argument.
 * Args: 
 * 	char **s:
 * 		Address of the pointer to the string we are looking at.
 * 	const char *delim:
 * 		The set of delimiters.
 * Return value:
 *	The first token, copied by strndup (caller have to free it),
 * 	if a token is found, or NULL if isn't (os strndup fails)
 * 	*s points to the rest of the string
 */
char *firsttok(char **s, const char *delim)
{
	char *tok;
	char *rest;
	rest=strpbrk(*s,delim);
	if (!rest) {
		return NULL;
	}
#ifdef HAVE_STRNDUP
	tok=strndup(*s,rest-(*s));
#else
	{
		size_t len = rest - (*s);
		tok = malloc(sizeof(char) * (len + 1));
		memcpy(tok, *s, len);
		tok[len] = '\0';
	}
#endif
	if (!tok) {
		die("firsttok() -- strndup() failed");
	}
	*s=rest+1;
	return tok;
}

/*
read_config() -- Open and parse config file and extract values of variables
*/
bool_t read_config()
{
	char buf[(BUF_SZ + 1)], *p, *q, *r;
	bool_t user_config = True;
	FILE *fp;

	/* no need for child processes to re-read config */
	if(config_file) {
		return True;
	}
	
	if(config_file == (char *)NULL) {
		char *home_config = getenv("HOME");
		if (home_config != (char*)NULL) {
			config_file = malloc(strlen(home_config)+10);
			if (config_file == (char*)NULL) {
				die("parse_config() -- malloc() failed");
			}
			config_file = strcpy(config_file, home_config);
			config_file = strcat(config_file, "/.ssmtprc");
			if (access(config_file, F_OK) == -1) {
				free(config_file);
				config_file = NULL;
			}
		}

		if(config_file == (char *)NULL) {
			user_config = False;
			config_file = strdup(CONFIGURATION_FILE);
			if(config_file == (char *)NULL) {
				die("parse_config() -- strdup() failed");
			}
		}
	}

	if(user_config) {
		/* we don't need suid/guid when
		 * running as a regular user */
		if(setegid(getgid()) == -1 || seteuid(getuid()) == -1) {
			if(log_level > 0) {
				log_event(LOG_ERR, "Failed to set gid/uid");
			}
		}
	}

	if((fp = fopen(config_file, "r")) == NULL) {
		return(False);
	}

	while(fgets(buf, sizeof(buf), fp)) {
		char *begin=buf;
		char *rightside;
		/* Make comments invisible */
		p = buf;
		while(*p) {
			if(*p == '#') {
				*p = '\0';
				break;
			}
			if(*p == ' ' || *p == '\t') {
				p++;
				continue;
			}
			break;
		}

		/* Ignore malformed lines and comments */
		if(strchr(buf, '=') == (char *)NULL) continue;

		/* Parse out keywords */
		p=firsttok(&begin, "= \t\n");
		if(p){
			rightside=begin;
			q = firsttok(&begin, "= \t\n");
		}
		if(p && q) {
			if(strcasecmp(p, "Root") == 0) {
				if (user_config == True) {
					log_event(LOG_ERR, "Set Root=\"%s\" is invalid in .ssmtprc\n", q);
				}
				else {
					if((root = strdup(q)) == (char *)NULL) {
						die("parse_config() -- strdup() failed");
					}

					if(log_level > 0) {
						log_event(LOG_INFO, "Set Root=\"%s\"\n", root);
					}
				}
			}
			else if(user_config == True && strcasecmp(p, "EmailAddress") == 0) {
				if((uad = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}
				if(log_level > 0) {
					log_event(LOG_INFO, "Set EmailAddress=\"%s\"\n", uad);
				}
			}
			else if(user_config == True && strcasecmp(p, "AuthAskPass") == 0) {
				if((auth_askpass = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}
				if(log_level > 0) {
					log_event(LOG_INFO, "Set PasswordProgram=\"%s\"\n", auth_askpass);
				}
			}
			else if(strcasecmp(p, "QueueDir") == 0) {
				if(q[0] == '~') {
					struct passwd *pw;
					pw = getpwuid(getuid());
					if(!pw) {
						die("parse_config() -- getpwuid() failed");
					}
					queue_dir = malloc(strlen(pw->pw_dir) + strlen(q));
					if(queue_dir == (char *)NULL) {
						die("parse_config() -- malloc() failed");
					}
					strcpy(queue_dir, pw->pw_dir);
					strcat(queue_dir, q+1);
				}
				else {
					if((queue_dir = strdup(q)) == (char *)NULL) {
						die("parse_config() -- strdup() failed");
					}
				}
				if(log_level > 0) {
					log_event(LOG_INFO, "Set QueueDir=\"%s\"\n", queue_dir);
				}
			}
			else if(strcasecmp(p, "MinUserId") == 0) {
				if((r = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}

				minuserid = atoi(r);
				free(r);

				if(log_level > 0) {
					log_event(LOG_INFO, "Set MinUserId=\"%d\"\n", minuserid);
				}
			}
			else if(strcasecmp(p, "MailHub") == 0) {
				if((r = strchr(q, ':')) != NULL) {
					*r++ = '\0';
					port = atoi(r);
				}

				if((mailhost = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}

				if(log_level > 0) {
					log_event(LOG_INFO, "Set MailHub=\"%s\"\n", mailhost);
					log_event(LOG_INFO, "Set RemotePort=\"%d\"\n", port);
				}
			}
			else if(strcasecmp(p, "HostName") == 0) {
				free(hostname);
				hostname = strdup(q);
				if (!hostname) {
					die("parse_config() -- strdup() failed");
				}

				if(log_level > 0) {
					log_event(LOG_INFO, "Set HostName=\"%s\"\n", hostname);
				}
			}
			else if(strcasecmp(p,"AddHeader") == 0) {
				if((r = firsttok(&rightside, "\n#")) != NULL) {
					header_save(r);
					free(r);
				} else {
					die("cannot AddHeader");
				}
				if(log_level > 0 ) {
					log_event(LOG_INFO, "Set AddHeader=\"%s\"\n", q);
				}
			}
#ifdef REWRITE_DOMAIN
			else if(strcasecmp(p, "RewriteDomain") == 0) {
				if((p = strrchr(q, '@'))) {
					mail_domain = strdup(++p);

					log_event(LOG_ERR,
						"Set RewriteDomain=\"%s\" is invalid\n", q);
					log_event(LOG_ERR,
						"Set RewriteDomain=\"%s\" used\n", mail_domain);
				}
				else {
					mail_domain = strdup(q);
				}

				if(mail_domain == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}
				rewrite_domain = True;

				if(log_level > 0) {
					log_event(LOG_INFO,
						"Set RewriteDomain=\"%s\"\n", mail_domain);
				}
			}
#endif
			else if(strcasecmp(p, "FromLineOverride") == 0) {
				if(strcasecmp(q, "YES") == 0) {
					override_from = True;
				}
				else {
					override_from = False;
				}

				if(log_level > 0) {
					log_event(LOG_INFO,
						"Set FromLineOverride=\"%s\"\n",
						override_from ? "True" : "False");
				}
			}
			else if(strcasecmp(p, "RemotePort") == 0) {
				port = atoi(q);

				if(log_level > 0) {
					log_event(LOG_INFO, "Set RemotePort=\"%d\"\n", port);
				}
			}
#ifdef HAVE_SSL
			else if(strcasecmp(p, "UseTLS") == 0) {
				if(strcasecmp(q, "YES") == 0) {
					use_tls = True;
				}
				else {
					use_tls = False;
					use_starttls = False;
				}

				if(log_level > 0) { 
					log_event(LOG_INFO,
						"Set UseTLS=\"%s\"\n", use_tls ? "True" : "False");
				}
			}
			else if(strcasecmp(p, "UseSTARTTLS") == 0) {
				if(strcasecmp(q, "YES") == 0) {
					use_starttls = True;
					use_tls = True;
				}
				else {
					use_starttls = False;
				}

				if(log_level > 0) { 
					log_event(LOG_INFO,
						"Set UseSTARTTLS=\"%s\"\n", use_tls ? "True" : "False");
				}
			}
			else if(strcasecmp(p, "UseTLSCert") == 0) {
				if(strcasecmp(q, "YES") == 0) {
					use_cert = True;
				}
				else {
					use_cert = False;
				}

				if(log_level > 0) {
					log_event(LOG_INFO,
						"Set UseTLSCert=\"%s\"\n",
						use_cert ? "True" : "False");
				}
			}
			else if(strcasecmp(p, "TLSCert") == 0) {
				if((tls_cert = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}

				if(log_level > 0) {
					log_event(LOG_INFO, "Set TLSCert=\"%s\"\n", tls_cert);
				}
			}
#endif
			/* Command-line overrides these */
			else if(strcasecmp(p, "AuthUser") == 0 && !auth_user) {
				if((auth_user = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}

				if(log_level > 0) {
					log_event(LOG_INFO, "Set AuthUser=\"%s\"\n", auth_user);
				}
			}
			else if(strcasecmp(p, "AuthPass") == 0 && !auth_pass) {
				auth_pass = firsttok(&rightside, " \n\t");
				if(auth_pass  == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}

				if(log_level > 0) {
					#if 0
					log_event(LOG_INFO, "Set AuthPass=\"%s\"\n", auth_pass);
					#else
					log_event(LOG_INFO, "Set AuthPass=\"XXXXXX\"\n");
					#endif
				}
			}
			else if(strcasecmp(p, "AuthMethod") == 0 && !auth_method) {
				if((auth_method = strdup(q)) == (char *)NULL) {
					die("parse_config() -- strdup() failed");
				}

				if(log_level > 0) {
					log_event(LOG_INFO, "Set AuthMethod=\"%s\"\n", auth_method);
				}
			}
			else if(strcasecmp(p, "UseOldAUTH") == 0) {
				if(strcasecmp(q, "YES") == 0) {
					use_oldauth = True;
				}
				else {
					use_oldauth = False;
				}
 
				if(log_level > 0) {
					log_event(LOG_INFO,
						"Set UseOldAUTH=\"%s\"\n",
						use_oldauth ? "True" : "False");
				}
			}
			else if (strcasecmp(p, "Debug") == 0)
			{
				if (strcasecmp(q, "YES") == 0)
				{
					log_level = 1;
				}
				else
				{
					log_level = 0;
				}
			}
			else {
				log_event(LOG_INFO, "Unable to set %s=\"%s\"\n", p, q);
			}
			free(p);
			free(q);
		} 
	}
	(void)fclose(fp);

	return(True);
}

/*
auth_getpass() -- Request a password from password program
*/
char *auth_getpass(void)
{
	int fd_pipe[2], pid;
	if (pipe(fd_pipe) == -1) {
		die("auth_getpass() -- pipe() failed");
	}
	pid = fork();
	if(pid == -1) {
		die("auth_getpass() -- fork() failed");
	}
	else if(pid == 0) {
		char *pw_conv;
		int r;
		if (dup2(fd_pipe[1], STDOUT_FILENO) == -1) {
			die("auth_getpass() -- dup2() failed");
		}
		close(fd_pipe[0]);
		if (getuid() != geteuid()) {
			r = seteuid(getuid());
		}
		if(getgid() != getegid()) {
			r = setegid(getgid());
		}
		pw_conv = malloc(strlen(auth_user) + (20 * sizeof(char)));
		if (pw_conv == (char *)NULL) {
			die("child: auth_getpass() -- malloc() failed");
		}
		if(sprintf(pw_conv, "Password 'ssmtp//%s':", auth_user) < 0) {
			die("child: auth_getpass() -- sprintf() failed");
		}
		execv(auth_askpass, (char * const[]){ auth_askpass, pw_conv, NULL });
		die("child: auth_getpass() -- execv() failed");
		if(r) {
			exit(0);
		}
	}
	else {
		int exit_code, buf_len = 0, pw_len = 0, r;
		char *pw_buf = NULL;
		close(fd_pipe[1]);
		wait(&exit_code);
		if(exit_code) {
			die("Operation cancelled");
		}
		while(1) {
			buf_len += 16;
			pw_buf = realloc(pw_buf, (buf_len * sizeof(char))+1);
			if(pw_buf == (char *)NULL) {
				die("auth_getpass() -- realloc() failed");
			}
			r = read(fd_pipe[0], pw_buf + pw_len, 16);
			if (r <= 0) {
				break;
			}
			pw_len += r;
			pw_buf[pw_len] = '\0';
		}
		if (r != 0 || !pw_len) {
			return NULL;
		}
		return pw_buf;
	}
}

#if HAVE_SSL
void ssl_error(SSL* ssl, int err)
{
	switch(SSL_get_error(ssl, err)) {
	case SSL_ERROR_ZERO_RETURN: die("SSL Error: SSL_ERROR_ZERO_RETURN\n");
	case SSL_ERROR_WANT_READ: die("SSL Error: SSL_ERROR_WANT_READ\n");
	case SSL_ERROR_WANT_WRITE: die("SSL Error: SSL_ERROR_WANT_WRITE\n");
	#if !HAVE_GNUTLS
	case SSL_ERROR_WANT_CONNECT: die("SSL Error: SSL_ERROR_WANT_CONNECT\n");
	case SSL_ERROR_WANT_ACCEPT: die("SSL Error: SSL_ERROR_WANT_ACCEPT\n");
	case SSL_ERROR_WANT_X509_LOOKUP: die("SSL Error: SSL_ERROR_WANT_X508_LOOKUP\n");
	#endif
	case SSL_ERROR_SYSCALL: die("SSL Error: SSL_ERROR_SYSCALL\n");
	case SSL_ERROR_SSL: 
		#if !HAVE_GNUTLS
		if(minus_v) {
			ERR_print_errors_fp (stderr);
		}
		#endif
		die("SSL Error: SSL_ERROR_SSL\n");
	}
}
#endif

/*
smtp_open() -- Open connection to a remote SMTP listener
*/
int smtp_open(char *host, int port)
{
#ifdef INET6
	struct addrinfo hints, *ai0, *ai;
	char servname[NI_MAXSERV];
	int s;
#else
	struct sockaddr_in name;
	struct hostent *hent;
	int i, s, namelen;
#endif

#ifdef HAVE_SSL
	int err;
	char buf[(BUF_SZ + 1)];

	/* Init SSL stuff */
	SSL_CTX *ctx;
	SSL_METHOD *meth;
	const X509 *server_cert;

	SSL_load_error_strings();
	SSLeay_add_ssl_algorithms();
	meth=SSLv23_client_method();
	ctx = SSL_CTX_new(meth);
	if(!ctx) {
		log_event(LOG_ERR, "No SSL support initiated\n");
		return(-1);
	}

	if(use_cert == True) { 
#ifdef HAVE_GNUTLS
		if(SSL_CTX_use_certificate_file(ctx, tls_cert, SSL_FILETYPE_PEM) <= 0) {
#else
		if(SSL_CTX_use_certificate_chain_file(ctx, tls_cert) <= 0) {
#endif
			perror("Use certfile");
			return(-1);
		}

		if(SSL_CTX_use_PrivateKey_file(ctx, tls_cert, SSL_FILETYPE_PEM) <= 0) {
			perror("Use PrivateKey");
			return(-1);
		}

#ifndef HAVE_GNUTLS
		if(!SSL_CTX_check_private_key(ctx)) {
			log_event(LOG_ERR, "Private key does not match the certificate public key\n");
			return(-1);
		}
#endif
	}
#endif

#ifdef INET6
	memset(&hints, 0, sizeof(hints));
	hints.ai_family = p_family;
	hints.ai_socktype = SOCK_STREAM;
	snprintf(servname, sizeof(servname), "%d", port);

	/* Check we can reach the host */
	if (getaddrinfo(host, servname, &hints, &ai0)) {
		log_event(LOG_ERR, "Unable to locate %s", host);
		return(-1);
	}

	for (ai = ai0; ai; ai = ai->ai_next) {
		/* Create a socket for the connection */
		s = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
		if (s < 0) {
			continue;
		}

		if (connect(s, ai->ai_addr, ai->ai_addrlen) < 0) {
			s = -1;
			continue;
		}
		break;
	}

	freeaddrinfo(ai0);

	if(s < 0) {
		log_event (LOG_ERR,
			"Unable to connect to \"%s\" port %d.\n", host, port);
		return(-1);
	}
#else
	/* Check we can reach the host */
	if((hent = gethostbyname(host)) == (struct hostent *)NULL) {
		log_event(LOG_ERR, "Unable to locate %s", host);
		return(-1);
	}

	if(hent->h_length > sizeof(hent->h_addr)) {
		log_event(LOG_ERR, "Buffer overflow in gethostbyname()");
		return(-1);
	}

	/* Create a socket for the connection */
	if((s = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) < 0) {
		log_event(LOG_ERR, "Unable to create a socket");
		return(-1);
	}
	
	for (i = 0; ; ++i) {
		if (!hent->h_addr_list[i]) {
			log_event(LOG_ERR, "Unable to connect to %s:%d", host, port);
			return(-1);
		}

	/* This SHOULD already be in Network Byte Order from gethostbyname() */
	name.sin_addr.s_addr = ((struct in_addr *)(hent->h_addr_list[i]))->s_addr;
	name.sin_family = hent->h_addrtype;
	name.sin_port = htons(port);

	namelen = sizeof(struct sockaddr_in);
	if(connect(s, (struct sockaddr *)&name, namelen) < 0)
		continue;
	break;
	}
#endif

#ifdef HAVE_SSL
	if(use_tls == True) {
		log_event(LOG_INFO, "Creating SSL connection to host");

		if (use_starttls == True)
		{
			use_tls=False; /* need to write plain text for a while */

			if (smtp_okay(s, buf))
			{
				smtp_write(s, "EHLO %s", hostname);
				if (smtp_okay(s, buf)) {
					smtp_write(s, "STARTTLS"); /* assume STARTTLS regardless */
					if (!smtp_okay(s, buf)) {
						log_event(LOG_ERR, "STARTTLS not working");
						return(-1);
					}
				}
				else
				{
					log_event(LOG_ERR, "Invalid response: %s (%s)", buf, hostname);
				}
			}
			else
			{
				log_event(LOG_ERR, "Invalid response SMTP Server (STARTTLS)");
				return(-1);
			}
			use_tls=True; /* now continue as normal for SSL */
		}

		ssl = SSL_new(ctx);
		if(!ssl) {
			log_event(LOG_ERR, "SSL not working");
			return(-1);
		}
		SSL_set_fd(ssl, s);

		err = SSL_connect(ssl);
		if(err < 0) { 
			ssl_error(ssl, err);
			return(-1);
		}

		if(log_level > 0 || 1) {
			log_event(LOG_INFO, "SSL connection using %s",
				SSL_get_cipher(ssl));
		}

		server_cert = SSL_get_peer_certificate(ssl);
		if(!server_cert) {
			return(-1);
		}
		X509_free(server_cert);

		/* TODO: Check server cert if changed! */
	}
#endif

	return(s);
}

/*
fd_getc() -- Read a character from an fd
*/
ssize_t fd_getc(int fd, void *c)
{
#ifdef HAVE_SSL
	if(use_tls == True) { 
		return(SSL_read(ssl, c, 1));
	}
#endif
	return(read(fd, c, 1));
}

/*
fd_gets() -- Get characters from a fd instead of an fp
*/
char *fd_gets(char *buf, int size, int fd)
{
	int i = 0;
	char c;

	while((i < size) && (fd_getc(fd, &c) == 1)) {
		if(c == '\r');	/* Strip <CR> */
		else if(c == '\n') {
			break;
		}
		else {
			buf[i++] = c;
		}
	}
	buf[i] = '\0';

	return(buf);
}

/*
smtp_read() -- Get a line and return the initial digit
*/
int smtp_read(int fd, char *response)
{
	do {
		if(fd_gets(response, BUF_SZ, fd) == NULL) {
			return(0);
		}
	}
	while(response[3] == '-');

	if(log_level > 0) {
		log_event(LOG_INFO, "%s\n", response);
	}

	if(minus_v) {
		(void)fprintf(stderr, "[<-] %s\n", response);
	}

	return(atoi(response) / 100);
}

/*
smtp_okay() -- Get a line and test the three-number string at the beginning
				If it starts with a 2, it's OK
*/
int smtp_okay(int fd, char *response)
{
	return((smtp_read(fd, response) == 2) ? 1 : 0);
}

/*
fd_puts() -- Write characters to fd
*/
ssize_t fd_puts(int fd, const void *buf, size_t count) 
{
#ifdef HAVE_SSL
	if(use_tls == True) { 
		return(SSL_write(ssl, buf, count));
	}
#endif
	return(write(fd, buf, count));
}

/*
smtp_write() -- A printf to an fd and append <CR/LF>
*/
ssize_t smtp_write(int fd, char *format, ...)
{
	char buf[(BUF_SZ + 2)];
	va_list ap;
	ssize_t outbytes = 0;

	va_start(ap, format);
	if(vsnprintf(buf, (BUF_SZ - 1), format, ap) == -1) {
		die("smtp_write() -- vsnprintf() failed");
	}
	va_end(ap);

	if(log_level > 0) {
		log_event(LOG_INFO, "%s\n", buf);
	}

	if(minus_v) {
		(void)fprintf(stderr, "[->] %s\n", buf);
	}
	(void)strcat(buf, "\r\n");

	outbytes = fd_puts(fd, buf, strlen(buf));
	
	return (outbytes >= 0) ? outbytes : 0;
}

/*
handler() -- A "normal" non-portable version of an alarm handler
			Alas, setting a flag and returning is not fully functional in
			BSD: system calls don't fail when reading from a ``slow'' device
			like a socket. So we longjump instead, which is erronious on
			a small number of machines and ill-defined in the language
*/
void handler(void)
{
	extern jmp_buf TimeoutJmpBuf;

	longjmp(TimeoutJmpBuf, (int)1);
}

/*
ssmtp() -- send the message (exactly one) from stdin to the mailhub SMTP port
*/
int ssmtp(char *argv[])
{
	char b[(BUF_SZ + 2)], *buf = b+1, *p, *q;
	char *remote_addr;
	char *uad_save;
#ifdef MD5AUTH
	char challenge[(BUF_SZ + 1)];
#endif
	struct passwd *pw;
	int i, sock;
	uid_t uid;
	bool_t minus_v_save, leadingdot, linestart = True;
	int timeout = 0;
	int bufsize = sizeof(b)-1;

	b[0] = '.';
	outbytes = 0;
	ht = &headers;

	/* save recipient list, we'll need it for queueing */
	rcptv = argv;

	uid = getuid();
	if((pw = getpwuid(uid)) == (struct passwd *)NULL) {
		die("Could not find password entry for UID %d", uid);
	}
	get_arpadate(arpadate);

	if(read_config() == False) {
		log_event(LOG_INFO, "%s not found", config_file);
	}

	if((p = strtok(pw->pw_gecos, ";,"))) {
		if((gecos = strdup(p)) == (char *)NULL) {
			die("ssmtp() -- strdup() failed");
		}
	}

	/* this may have been defined on the user's .ssmtprc */
	if(uad == (char *)NULL){
		revaliases(pw);

		/* revaliases() may have defined this */
		if(uad == (char *)NULL) {
			uad = append_domain(pw->pw_name);
		}
	}

	rt = &rcpt_list;

	header_parse(stdin);

#if 1
	/* With FromLineOverride=YES set, try to recover sane MAIL FROM address */
	uad_save = uad;
	uad = append_domain(uad);
	if(uad_save && uad != uad_save) {
		free(uad_save);
	}
#endif

	from = from_format(uad, override_from);

	/* Now to the delivery of the message */
	(void)signal(SIGALRM, (void(*)())handler);	/* Catch SIGALRM */
	(void)alarm((unsigned) MAXWAIT);			/* Set initial timer */
	if(setjmp(TimeoutJmpBuf) != 0) {
		/* Then the timer has gone off and we bail out */
		die("Connection lost in middle of processing");
	}

	if(!mailhost) {
		die("No mail host configured");
	}

	sending = True;
	debug_print("Connecting to %s:%i...\n", mailhost, port);

	if((sock = smtp_open(mailhost, port)) == -1) {
		die("Cannot open %s:%d", mailhost, port);
	}
	else if (use_starttls == False) /* no initial response after STARTTLS */
	{
		if(smtp_okay(sock, buf) == False)
			die("Invalid response SMTP server");
	}

	/* If user supplied username and password, then try ELHO */
	if(auth_user) {
		outbytes += smtp_write(sock, "EHLO %s", hostname);
	}
	else {
		outbytes += smtp_write(sock, "HELO %s", hostname);
	}
	(void)alarm((unsigned) MEDWAIT);

	if(smtp_okay(sock, buf) == False) {
		comm_error = buf;
		die("%s (%s)", buf, hostname);
	}

	/* Try to log in if username was supplied */
	if(auth_user) {
		if(auth_pass == (char *)NULL) {
			if(auth_askpass != (char *)NULL) {
				auth_pass = auth_getpass();
			}
		}
#ifdef MD5AUTH
		if (auth_pass == (char *)NULL) {
			auth_pass = strdup("");
		}

		if(auth_method && strcasecmp(auth_method, "cram-md5") == 0) {
			outbytes += smtp_write(sock, "AUTH CRAM-MD5");
			(void)alarm((unsigned) MEDWAIT);

			if(smtp_read(sock, buf) != 3) {
				comm_error = buf;
				die("Server rejected AUTH CRAM-MD5 (%s)", buf);
			}
			strncpy(challenge, strchr(buf,' ') + 1, sizeof(challenge));

			memset(buf, 0, bufsize);
			crammd5(challenge, auth_user, auth_pass, buf);
		}
		else {
#endif
		if(auth_method && strcasecmp(auth_method, "login") == 0) {
			memset(buf, 0, bufsize);
			to64frombits(buf, (unsigned char*)auth_user, strlen(auth_user));
			if (use_oldauth) {
				outbytes += smtp_write(sock, "AUTH LOGIN %s", buf);
			}
			else {
				outbytes += smtp_write(sock, "AUTH LOGIN");
				(void)alarm((unsigned) MEDWAIT);
				if(smtp_read(sock, buf) != 3) {
					comm_error = buf;
					die("Server didn't like our AUTH LOGIN (%s)", buf);
				}
				/* we assume server asked us for Username */
				memset(buf, 0, bufsize);
				to64frombits(buf, (unsigned char*)auth_user, strlen(auth_user));
				outbytes += smtp_write(sock, buf);
			}

			(void)alarm((unsigned) MEDWAIT);
			if(smtp_read(sock, buf) != 3) {
				comm_error = buf;
				die("Server didn't accept AUTH LOGIN (%s)", buf);
			}
			memset(buf, 0, bufsize);

			to64frombits(buf, (unsigned char*)auth_pass, strlen(auth_pass));
		}
		else {
			char *authbuf = malloc((strlen(auth_user) * 2) + strlen(auth_pass) + 3);
			if(!authbuf) {
				die("Out of memory");
			}
			outbytes += smtp_write(sock, "AUTH PLAIN");
			alarm((unsigned) MEDWAIT);
			if(smtp_read(sock, buf) != 3) {
				comm_error = buf;
				die("Server didn't accept AUTH PLAIN");
			}
			if(!authbuf) {
				die("out of memory");
			}
			memset(buf, 0, bufsize);
			strcpy(authbuf, auth_user);
			strcpy(authbuf+1+strlen(auth_user), auth_user);
			strcpy(authbuf+2+(2*strlen(auth_user)), auth_pass);
			to64frombits(buf, (unsigned char*)authbuf, 
				(strlen(auth_user)*2)+strlen(auth_pass)+2);
			free(authbuf);
		}

#ifdef MD5AUTH
		}
#endif
		/* We do NOT want the password output to STDERR
		 * even base64 encoded.*/
		minus_v_save = minus_v;
		minus_v = False;
		outbytes += smtp_write(sock, "%s", buf);
		minus_v = minus_v_save;
		(void)alarm((unsigned) MEDWAIT);

		if(smtp_okay(sock, buf) == False) {
			comm_error = buf;
			die("Authorization failed (%s)", buf);
		}
	}

	/* Send "MAIL FROM:" line */
	outbytes += smtp_write(sock, "MAIL FROM:<%s>", uad);

	(void)alarm((unsigned) MEDWAIT);

	if(smtp_okay(sock, buf) == 0) {
		comm_error = buf;
		die("%s", buf);
	}

	/* Send all the To: adresses */
	/* Either we're using the -t option, or we're using the arguments */
	if(minus_t) {
		if(rcpt_list.next == (rcpt_t *)NULL) {
			die("No recipients specified although -t option used");
		}
		rt = &rcpt_list;

		while(rt->next) {
			p = rcpt_remap(rt->string);
			outbytes += smtp_write(sock, "RCPT TO:<%s>", p);

			(void)alarm((unsigned)MEDWAIT);

			if(smtp_okay(sock, buf) == 0) {
				die("RCPT TO:<%s> (%s)", p, buf);
			}

			rt = rt->next;
		}
	}
	else {
		for(i = 1; (argv[i] != NULL); i++) {
			p = strtok(argv[i], ",");
			while(p) {
				/* RFC822 Address -> "foo@bar" */
				q = rcpt_remap(addr_parse(p));
				outbytes += smtp_write(sock, "RCPT TO:<%s>", q);

				(void)alarm((unsigned) MEDWAIT);

				if(smtp_okay(sock, buf) == 0) {
					die("RCPT TO:<%s> (%s)", q, buf);
				}

				p = strtok(NULL, ",");
			}
		}
	}

	/* Send DATA */
	outbytes += smtp_write(sock, "DATA");
	(void)alarm((unsigned) MEDWAIT);

	if(smtp_read(sock, buf) != 3) {
		/* Oops, we were expecting "354 send your data" */
		comm_error = buf;
		die("%s", buf);
	}

	outbytes += smtp_write(sock,
		"Received: by %s (sSMTP-Reloaded sendmail emulation); %s", hostname, arpadate);

	if(have_from == False) {
		outbytes += smtp_write(sock, "From: %s", from);
	}

	if((remote_addr=getenv("REMOTE_ADDR"))) {
		outbytes += smtp_write(sock, "X-Originating-IP: %s", remote_addr);
	}

	if(have_date == False) {
		outbytes += smtp_write(sock, "Date: %s", arpadate);
	}

#ifdef HASTO_OPTION
	if(have_to == False) {
		outbytes += smtp_write(sock, "To: postmaster");
	}
#endif

	ht = &headers;
	while(ht->next) {
		outbytes += smtp_write(sock, "%s", ht->string);
		ht = ht->next;
	}

	(void)alarm((unsigned) MEDWAIT);

	/* End of headers, start body */
	outbytes += smtp_write(sock, "");

	/*prevent blocking on pipes, we really shouldnt be using
	  stdio functions like fgets in the first place */
	fcntl(STDIN_FILENO,F_SETFL,O_NONBLOCK);

	while(!feof(stdin)) {
		if (!fgets(buf, bufsize, stdin)) {
			/* if nothing was received, then no transmission
			 * over smtp should be done */
			sleep(1);
			/* don't hang forever when reading from stdin */
			if (++timeout >= MEDWAIT) {
				log_event(LOG_ERR, "killed: timeout on stdin while reading body -- message saved to dead.letter.");
				die("Timeout on stdin while reading body");
			}
			continue;
		}
		/* Trim off \n, double leading .'s */
		leadingdot = standardise(buf, &linestart);

		if (linestart || feof(stdin)) {
			linestart = True;
			outbytes += smtp_write(sock, "%s", leadingdot ? b : buf);
		} else {
			if (log_level > 0) {
				log_event(LOG_INFO, "Sent a very long line in chunks");
			}
			if (leadingdot) {
				outbytes += fd_puts(sock, b, sizeof(b));
			} else {
				outbytes += fd_puts(sock, buf, bufsize);
			}
		}
		(void)alarm((unsigned) MEDWAIT);
	}
	if(!linestart) {
		smtp_write(sock, "");
	}
	/* End of body */

	outbytes += smtp_write(sock, ".");
	(void)alarm((unsigned) MAXWAIT);

	if(smtp_okay(sock, buf) == 0) {
		comm_error = buf;
		die("%s", buf);
	}

	/* Close connection */
	(void)signal(SIGALRM, SIG_IGN);

	outbytes += smtp_write(sock, "QUIT");
	(void)smtp_okay(sock, buf);
	(void)close(sock);

	log_event(LOG_INFO, "Sent mail for %s (%s) uid=%d username=%s outbytes=%d", 
		from_strip(uad), buf, uid, pw->pw_name, outbytes);

	return(0);
}

/*
paq() - Write error message and exit
*/
void paq(char *format, ...)
{
	va_list ap;   

	va_start(ap, format);
	(void)vfprintf(stderr, format, ap);
	va_end(ap);

	exit(0);
}

/*
queue_process() -- Process queued messages
*/
void __attribute__((noreturn)) 
queue_process(unsigned long interval, bool_t dofork, bool_t list_only)
{
	int pid, fd_pipe[2], fd_lock, r;
	unsigned long inttmp;
	bool_t found_some = False;

	if(dofork) {
		pid = fork();
		if(pid == -1) {
			log_event(LOG_ERR, "Could not daemonize: fork() failed");
			fprintf(stderr, "Could not daemonize: fork() failed\n");
			exit(1);
		}
		else if(pid != 0) {
			exit(0);
		}

		/* I'm not exactly sure what the purpose of
		 * "becoming bulletproof" is in main() but
		 * definitely not something we want when running
		 * as a daemon
		 */
		signal(SIGHUP, SIG_DFL);
		signal(SIGINT, SIG_DFL);
	}
	else {
		if(read_config() == False) {
			fprintf(stderr, "Could not read '%s'\n", config_file);
			exit(1);
		}
	}
	if(queue_dir == (char *)NULL) {
		paq("%s: Mail queue is empty\n", prog);
	}
	if(chdir(queue_dir) == -1) {
		log_event(LOG_ERR, "Could not access queue directory: %s", queue_dir);
		fprintf(stderr, "Could not access queue directory: %s\n", queue_dir);
		exit(1);
	}
	if(list_only) {
		printf("-Queue ID-\t-Size-\t\t----Arrival Time---\t\t-Sender/Recipient-\n");
	}

	while (1)
	{
		#define BUFSZ 64
		DIR *qdir;
		struct dirent *dp;
		FILE *f;
		char *to, *saved_uad, *err, buf[BUFSZ];
		struct stat stats;
		int s, slen;

		/* if we're processing the queue, lock it */
		if (!list_only) {
			if((fd_lock = creat(".queue-lock",
				S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP)) == -1) {
				log_event(LOG_ERR, "Could not access %s/.queue-lock", queue_dir);
				fprintf(stderr, "Could not lock queue: could not access %s/.queue-lock\n", 
					queue_dir);
				exit(1);
			}
			r = chown(".queue-lock", 0, getegid());
			r = chmod(".queue-lock", S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP);
			while(lockf(fd_lock, F_TLOCK, 0) != 0) {
				sleep(1);
			}
		}

		qdir = opendir(queue_dir);
		if(qdir == NULL) {
			paq("%s: Mail queue is empty\n", prog);
		}

		while((dp = readdir(qdir)) != NULL) {
			if(dp->d_name[0] == '.') {
				continue;
			}
			if(stat(dp->d_name, &stats) == -1) {
				continue;
			}
			if((r = getuid()) != 0 && r != stats.st_uid) {
				continue;
			}
			if((f = fopen(dp->d_name, "r")) == NULL) {
				fprintf(stderr, "%s: Cannot open: '%s/%s'. Skipping\n",
					prog, queue_dir, dp->d_name);
				continue;
			}
			if(fgets(buf, 7, f) != buf || strcmp(buf, "sSMTP:")) {
				fclose(f);
				continue;
			}
			found_some = True;
			to = err = NULL;
			s = 0;
			slen = 0;
			while ((r = fgetc(f)) != EOF) {
				if((char)r == '\n') {
					break;
				}
				if(slen >= s) {
					s += BUFSZ;
					to = realloc(to, s + 1);
					if(!to) {
						log_event(LOG_ERR, "Could not process '%s/%s': out of memory", 
							queue_dir, dp->d_name);
						fprintf(stderr, "%s: Could not process '%s/%s': out of memory\n",
							prog, queue_dir, dp->d_name);
						/* cleanup and continue done in
						 * next if statemeent */
						break;
					}
				}
				to[slen++] = (char) r;
			}
			if(!to) {
				log_event(LOG_ERR, "Invalid mail format: %s/%s",
					queue_dir, dp->d_name);
				fclose(f);
				continue;
			}
			else {
				to[slen] = '\0';
			}
			while(--slen) {
				if(to[slen] == '|') {
					to[slen] = '\0';
					err = to + slen + 1;
				}
			}

			if(list_only) {
				struct tm *tm;
				char sdate[40] = "                   \t";
				const char *delim = "";
				r = 0;

				headers_free();
				rcpt_free();
				ht = &headers;
				rt = &rcpt_list;
				minus_t = True;
				header_parse(f);

				r = (int) stats.st_size;
				tm = localtime(&stats.st_mtime);
				strftime(sdate, sizeof(sdate), nl_langinfo(D_T_FMT), tm);

				saved_uad = uad;
				if(!from) {
					struct passwd *pw;
					if((pw = getpwuid(stats.st_uid)) == NULL) {
						fclose(f);
						free(to);
						continue;
					}
					revaliases(pw);
					if(!uad) {
						uad = append_domain(pw->pw_name);
					}
				}

				printf("%s\t%i\t\t%s\t%s\n", dp->d_name, r, sdate, uad);
				if(err) {
					printf("%s\n", err);
				}
				printf("          \t      \t\t                   \t\t");

				if(!strcmp(to, "-t")) {
					rt = &rcpt_list;
					while(rt->next) {
						char *q;
						if((q = rcpt_remap(rt->string)) == NULL) {
							log_event(LOG_ERR, "Could not process '%s': out of memory",
								dp->d_name);
							fprintf(stderr, "%s: Out of memory in queue_process(), skipping '%s'\n",
								prog, dp->d_name);
							fclose(f);
							free(to);
							continue;
						}
						printf("%s%s", delim, q);
						delim = ",";
						rt = rt->next;
						free(q);
					}
					printf("\n\n");
				}
				else {
					printf("%s\n\n", to);
				}

				/* not ideal but it'll do for now */
				if(saved_uad != uad) {
					free(uad);
					uad = saved_uad;
				}

				fclose(f);
				free(to);
				continue;
			}

			if(pipe(fd_pipe) == -1) {
				log_event(LOG_ERR, "Skipped '%s/%s': pipe() failed",
					queue_dir, dp->d_name);
				fprintf(stderr, "%s: Skipped '%s/%s': pipe() failed\n",
					prog, queue_dir, dp->d_name);
				fclose(f);
				free(to);
				continue;
			}
			if((pid = fork()) == -1) {
				log_event(LOG_ERR, "Skipped '%s/%s': fork() failed",
					queue_dir, dp->d_name);
				fprintf(stderr, "%s: Skipped '%s/%s': fork() failed\n",
					prog, queue_dir, dp->d_name);
				fclose(f);
				free(to);
				continue;
			}
			else if(pid != 0) {
				close(fd_pipe[0]);
				while(!feof(f)) {
					r = fread(buf, sizeof(char), BUFSZ, f);
					if(r > 0) {
						if(write(fd_pipe[1], buf, r) == -1) {
							break;
						}
					}
				}
				close(fd_pipe[1]);
				fclose(f);
				free(to);
				wait(&r);

				if (!r) {
					unlink(dp->d_name);
				}
			}
			else {
				fclose(f);
				close(fd_pipe[1]);
				if(dup2(fd_pipe[0], STDIN_FILENO) == -1) {
					die("queue_process() -- dup2() failed");
				}

				/* if this is root sending of behalf of
				 * another user impersonate that user */
				if(getuid() != stats.st_uid) {
					if(setuid(stats.st_uid) == -1) {
						log_event(LOG_ERR, "Could not send %s/%s: setuid() failed",
							queue_dir, dp->d_name);
						die("Could not send %s/%s: setuid() failed",
							queue_dir, dp->d_name);
					}
				}
				do_not_queue = True;
				exit(main(2, (char*[]){ prog, to, NULL }));
			}
		}

		closedir(qdir);

		if(!list_only) {
			close(fd_lock);
		}

		if(!interval) {
			break;
		}

		inttmp = interval;
		while(inttmp > UINT_MAX) {
			sleep(UINT_MAX);
			inttmp -= UINT_MAX;
		}
		sleep((unsigned int) inttmp);
		#undef BUFSZ
	}

	if(!found_some) {
		paq("%s: Mail queue is empty\n", prog);
	}
	exit(0);
}

/*
parse_options() -- Pull the options out of the command-line
	Process them (special-case calls to mailq, etc) and return the rest
*/
char **parse_options(int argc, char *argv[])
{
	static char Version[] = VERSION;
	static char *new_argv[MAXARGS];
	int i, j, l, add, new_argc; 
	unsigned long interval = 0;
	bool_t daemonize = False, fork = False, proc_queue = False,
		done = False;

	new_argv[0] = argv[0];
	new_argc = 1;

	if(strcmp(prog, "mailq") == 0) {
		/* Someone wants to know the queue state... */
		queue_process(0, False, True);
		exit(0);
	}
	else if(strcmp(prog, "newaliases") == 0) {
		/* Someone wanted to rebuild aliases */
		paq("newaliases: Aliases are not used in sSMTP-Reloaded\n");
	}

	i = 1;
	while(i < argc) {
		if(argv[i][0] != '-') {
			new_argv[new_argc++] = argv[i++];
			continue;
		}
		j = 0;

		add = 1;
		while(argv[i][++j] != '\0') {
			switch(argv[i][j]) {
#ifdef INET6
			case '6':
				p_family = PF_INET6;
				continue;

			case '4':
				p_family = PF_INET;
			continue;
#endif

			case 'a':
				switch(argv[i][++j]) {
				case 'u':
					if((!argv[i][(j + 1)])
						&& argv[(i + 1)]) {
						auth_user = strdup(argv[i+1]);
						if(auth_user == (char *)NULL) {
							die("parse_options() -- strdup() failed");
						}
						add++;
					}
					else {
						auth_user = strdup(argv[i]+j+1);
						if(auth_user == (char *)NULL) {
							die("parse_options() -- strdup() failed");
						}
					}
					goto exit;

				case 'p':
					if((!argv[i][(j + 1)])
						&& argv[(i + 1)]) {
						auth_pass = strdup(argv[i+1]);
						if(auth_pass == (char *)NULL) {
							die("parse_options() -- strdup() failed");
						}
						add++;
					}
					else {
						auth_pass = strdup(argv[i]+j+1);
						if(auth_pass == (char *)NULL) {
							die("parse_options() -- strdup() failed");
						}
					}
					goto exit;

/*
#ifdef MD5AUTH
*/
				case 'm':
					if(!argv[i][j+1]) { 
						auth_method = strdup(argv[i+1]);
						add++;
					}
					else {
						auth_method = strdup(argv[i]+j+1);
					}
				}
				goto exit;
/*
#endif
*/

			case 'b':
				switch(argv[i][++j]) {

				case 'a':	/* ARPANET mode */
						paq("-ba is not supported by sSMTP-Reloaded\n");
				case 'd':	/* Run as a daemon */
						daemonize = True;
						fork = True;
						break;
				case 'i':	/* Initialise aliases */
						paq("%s: Aliases are not used in sSMTP-Reloaded\n", prog);
				case 'm':	/* Default addr processing */
						continue;

				case 'p':	/* Print mailqueue */
						queue_process(0, False, True);
						exit(0);
				case 's':	/* Read SMTP from stdin */
						paq("-bs is not supported by sSMTP-Reloaded\n");
				case 't':	/* Test mode */
						paq("-bt is meaningless to sSMTP-Reloaded\n");
				case 'v':	/* Verify names only */
						paq("-bv is meaningless to sSMTP-Reloaded\n");
				case 'z':	/* Create freeze file */
						paq("-bz is meaningless to sSMTP-Reloaded\n");
				}

			/* Configfile name */
			case 'C':
				if((!argv[i][(j + 1)]) && argv[(i + 1)]) {
					config_file = strdup(argv[(i + 1)]);
					if(config_file == (char *)NULL) {
						die("parse_options() -- strdup() failed");
					}
					add++;
				}
				else {
					config_file = strdup(argv[i]+j+1);
					if(config_file == (char *)NULL) {
						die("parse_options() -- strdup() failed");
					}
				}
				goto exit;

			/* Debug */
			case 'd':
				log_level = 1;
				/* Almost the same thing... */
				minus_v = True;

				continue;

			/* Insecure channel, don't trust userid */
			case 'E':
					continue;

			case 'R':
				/* Amount of the message to be returned */
				if(!argv[i][j+1]) {
					add++;
					goto exit;
				}
				else {
					/* Process queue for recipient */
					continue;
				}

			/* Fullname of sender */
			case 'F':
				if((!argv[i][(j + 1)]) && argv[(i + 1)]) {
					minus_F = strdup(argv[(i + 1)]);
					if(minus_F == (char *)NULL) {
						die("parse_options() -- strdup() failed");
					}
					add++;
				}
				else {
					minus_F = strdup(argv[i]+j+1);
					if(minus_F == (char *)NULL) {
						die("parse_options() -- strdup() failed");
					}
				}
				goto exit;

			/* Set from/sender address */
			case 'f':
			/* Obsolete -f flag */
			case 'r':
				if((!argv[i][(j + 1)]) && argv[(i + 1)]) {
					minus_f = strdup(argv[(i + 1)]);
					if(minus_f == (char *)NULL) {
						die("parse_options() -- strdup() failed");
					}
					add++;
				}
				else {
					minus_f = strdup(argv[i]+j+1);
					if(minus_f == (char *)NULL) {
						die("parse_options() -- strdup() failed");
					}
				}
				goto exit;

			/* Set hopcount */
			case 'h':
				continue;

			/* Ignore originator in adress list */
			case 'm':
				continue;

			/* Use specified message-id */
			case 'M':
				goto exit;

			/* DSN options */
			case 'N':
				add++;
				goto exit;

			/* No aliasing */
			case 'n':
				continue;

			case 'o':
				switch(argv[i][++j]) {

				/* Alternate aliases file */
				case 'A':
					goto exit;

				/* Delay connections */
				case 'c':
					continue;

				/* Run newaliases if required */
				case 'D':
					paq("%s: Aliases are not used in sSMTP-Reloaded\n", prog);

				/* Deliver now, in background or queue */
				/* This may warrant a diagnostic for b or q */
				case 'd':
						continue;

				/* Errors: mail, write or none */
				case 'e':
					j++;
					continue;

				/* Set tempfile mode */
				case 'F':
					goto exit;

				/* Save ``From ' lines */
				case 'f':
					continue;

				/* Set group id */
				case 'g':
					goto exit;

				/* Helpfile name */
				case 'H':
					continue;

				/* DATA ends at EOF, not \n.\n */
				case 'i':
					continue;

				/* Log level */
				case 'L':
					goto exit;

				/* Send to me if in the list */
				case 'm':
					continue;

				/* Old headers, spaces between adresses */
				case 'o':
					paq("-oo is not supported by sSMTP-Reloaded\n");

				/* Queue dir */
				case 'Q':
					goto exit;

				/* Read timeout */
				case 'r':
					goto exit;

				/* Always init the queue */
				case 's':
					continue;

				/* Stats file */
				case 'S':
					goto exit;

				/* Queue timeout */
				case 'T':
					goto exit;

				/* Set timezone */
				case 't':
					goto exit;

				/* Set uid */
				case 'u':
					goto exit;

				/* Set verbose flag */
				case 'v':
					minus_v = True;
					continue;
				}
				break;

			/* Process the queue [at time] */
			case 'q':
				done = False;
				proc_queue = True;
				while(done == False) {
					switch(argv[i][++j]) {
					case 'f':
						fork = False;
						break;
					case '\0':
						done = True;
						j--;
						break;
					default:
						if(isdigit(argv[i][j])) {
							char *num = &argv[i][j];
							while(*num) {
								l = 0;
								while(isdigit(num[++l]));
								switch(num[l]) {
								case 'm':
									num[l] = '\0';
									interval += strtoul(num, NULL, 10) * 60;
									break;
								case 's':
									num[l] = '\0';
									interval += strtoul(num, NULL, 10);
									break;
								case 'h':
									num[l] = '\0';
									interval += strtoul(num, NULL, 10) * 60 * 60;
									break;
								case 'd':
									num[l] = '\0';
									interval += strtoul(num, NULL, 10) * 60 * 60 * 24;
									break;
								case 'w':
									num[l] = '\0';
									interval += strtoul(num, NULL, 10) * 60 * 60 * 24 * 7;
									break;
								case '\0':
									if(num != &argv[i][j]) {
										die("Invalid argument\n");
									}
									num[l] = '\0';
									interval += strtoul(num, NULL, 10) * 60;
									goto breakout;
								default:
									die("Invalid argument\n");
								}
								num = &num[++l];
							}
							breakout:
							break;
						}
						break;
					}
				}
				break;

			/* Read message's To/Cc/Bcc lines */
			case 't':
				minus_t = True;
				continue;

			/* minus_v (ditto -ov) */
			case 'v':
				minus_v = True;
				break;

			/* Say version and quit */
			/* Similar as die, but no logging */
			case 'V':
				paq("sSMTP-Reloaded %s (Not sendmail at all)\n", Version);
			}
		}

		exit:
		i += add;
	}
	new_argv[new_argc] = NULL;

	if (daemonize && proc_queue == False) {
		paq("-bd is only supported by sSMTP-Reloaded when used with -q\n");
	}
	else if (proc_queue == True) {
		queue_process(interval, fork, False);
		exit(0);
	}

	if(new_argc <= 1 && !minus_t) {
		paq("%s: No recipients supplied - mail will not be sent\n", prog);
	}

	if(new_argc > 1 && minus_t) {
		paq("%s: recipients with -t option not supported\n", prog);
	}

	return(&new_argv[0]);
}

/*
main() -- make the program behave like sendmail, then call ssmtp
*/
int main(int argc, char **argv)
{
	char **new_argv;

	/* Try to be bulletproof :-) */
	(void)signal(SIGHUP, SIG_IGN);
	(void)signal(SIGINT, SIG_IGN);
	(void)signal(SIGTTIN, SIG_IGN);
	(void)signal(SIGTTOU, SIG_IGN);

	/* Set the globals */
	prog = xbasename(argv[0]);

	hostname = xgethostname();

	if(!hostname) {
		perror("xgethostname");
		die("Cannot get the name of this machine");
	}
	new_argv = parse_options(argc, argv);

	exit(ssmtp(new_argv));
}
