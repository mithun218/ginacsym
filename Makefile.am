## Process this file with automake to produce Makefile.in
#SUBDIRS = ginac check ginsh tools doc
#DIST_SUBDIRS = ginac check ginsh tools doc
SUBDIRS = ginacsym check
DIST_SUBDIRS = ginacsym check

# pkg-config metadata
pkgconfigdir = $(libdir)/pkgconfig
pkgconfig_DATA = ginacsym.pc
$(pkgconfig_DATA): config.status

CMAKE_FILES = CMakeLists.txt
DOC = doc

# All the rest of the distributed files
EXTRA_DIST = ginacsym.pc $(CMAKE_FILES) $(DOC)

# Rule to build tar-bzipped distribution package
$(PACKAGE)-$(VERSION).tar.gz: dist

# Rule to build RPM distribution package
rpm: $(PACKAGE)-$(VERSION).tar.gz
	rpmbuild -ta --clean $(PACKAGE)-$(VERSION).tar.gz


ACLOCAL_AMFLAGS = -I m4
