include src/Makefile.am
include test/Makefile.am

EXTRA_DIST = \
	src/Makefile.am \
	src/config.h.in \
	test/Makefile.am \
	example \
	README.md \
	README_DEV.md \
	$(veriT_DIST) \
	LICENSE

maintainer-clean-local:
	rm Makefile.in
	rm aclocal.m4
	rm configure
	rm src/config.h.in
	rm -f scripts/compile
	rm -f scripts/depcomp
	rm -f scripts/install-sh
	rm -f scripts/missing
	rm -f scripts/test-driver
	rm -f src/parsers/smtlib2/smtsyn.output

cleanse: maintainer-clean

