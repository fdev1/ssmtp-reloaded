sSMTP Reloaded
==============

sSMTP is a program that replaces sendmail on workstations that should
send their mail via the departmental mailhub from which they pick up their
mail (via pop, imap, rsmtp, pop_fetch, NFS... or the like).  This program
accepts mail and sends it to the mailhub, optionally replacing the domain in 
the From: line with a different one.

This fork includes the following improvements over the original sSMTP:

* Fixes a large number of warnings that are generated when compiling
  with a recent version of GCC;
* Added support for overriding the global configuration through
  individual users configuration files;
* Added support for storing user passwords in a keyring with the
  ssh-askpass program
* A number of minor bug fixes and alt platform support (mostly borrowed 
  from Gentoo's sSMTP patchset)
