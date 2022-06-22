export IDRIS2 ?= idris2
export TYRE ?= $(CURDIR)/build/ttc

.PHONY: build buildtests runtests

build:
	${IDRIS2} --build tyre.ipkg

install: build
	${IDRIS2} --install tyre.ipkg

buildtests:
	make -C tests testbin IDRIS2=${IDRIS2} IDRIS2_PATH=${TYRE}

runtests: install buildtests
	make -C tests test IDRIS2=${IDRIS2} IDRIS2_PATH=${TYRE} only=$(only)

clean:
	$(RM) -r build
	$(RM) -r **/**/build
	make -C tests clean
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
