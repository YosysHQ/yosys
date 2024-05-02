all: examples all_tex tidy

# set a fake time in pdf generation to prevent unnecessary differences in output
FAKETIME := TZ='Z' faketime -f '2022-01-01 00:00:00 x0,001'

# find all code example makefiles
.PHONY: examples
CODE_EXAMPLES := ../code_examples/*/Makefile
examples: $(CODE_EXAMPLES)

# target to convert specified dot file(s)
.PHONY: convert
TARG_DOT ?=
convert: $(TARG_DOT:.dot=.pdf) $(TARG_DOT:.dot=.svg)

# use empty FORCE target because .PHONY ignores % expansion, using find allows
# us to generate everything in one pass, since we don't know all of the possible
# outputs until the sub-makes run
FORCE:
../%/Makefile: FORCE
	@make -C $(@D) dots
	@mkdir -p $*
	@find $(@D) -name *.dot -exec cp -u {} -t $* \;
	@find $* -name *.dot -printf "%p " | xargs -i make --no-print-directory convert TARG_DOT="{}"

# find and build all tex files
.PHONY: all_tex
TEX_FILES := $(wildcard **/*.tex)
all_tex: $(TEX_FILES:.tex=.pdf) $(TEX_FILES:.tex=.svg)

%.pdf: %.dot
	$(FAKETIME) dot -Tpdf -o $@ $<

%.pdf: %.tex
	cd $(@D) && $(FAKETIME) pdflatex $(<F) --interaction=nonstopmode

%.svg: %.pdf
	pdf2svg $< $@

.PHONY: clean tidy
tidy:
	rm -f  **/*.log **/*.aux

clean: tidy
	rm -rf code_examples
	rm -f **/*.pdf **/*.svg
