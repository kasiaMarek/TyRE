INTERACTIVE ?= --interactive

.PHONY: testbin test

test:
	./build/exec/tyretests $(IDRIS2) $(INTERACTIVE) --failure-file failures --only $(only)

testbin:
	${IDRIS2} --build tests.ipkg

clean:
	$(RM) failures
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
