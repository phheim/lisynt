STACKPATH=$(shell stack path | grep local-install-root | sed 's/local-install-root: //')

default:
	stack build
	@cp ${STACKPATH}/bin/lisynt lisynt
	@cp ${STACKPATH}/bin/lisynt-bench lisynt-bench
	@cp ${STACKPATH}/bin/bltl2 bltl2

install:
	stack install

clean:
	stack clean
	@rm -f lisynt
	@rm -f lisynt-bench
	@rm -f bltl2

.PHONY: install clean 
.SILENT:
