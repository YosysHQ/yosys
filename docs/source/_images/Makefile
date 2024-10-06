all: examples all_tex

# set a fake time in pdf generation to prevent unnecessary differences in output
FAKETIME := TZ='Z' faketime -f '2022-01-01 00:00:00 x0,001'

# find all code example makefiles
.PHONY: examples
CODE_EXAMPLES := ../code_examples/*/Makefile
examples: $(CODE_EXAMPLES)

# target to convert all dot files
# needs to be run *after* examples, otherwise no dot files will be found
.PHONY: convert
DOT_FILES := $(shell find . -name *.dot)
convert: $(DOT_FILES:.dot=.pdf) $(DOT_FILES:.dot=.svg)

# use empty FORCE target because .PHONY ignores % expansion
FORCE:
../%/Makefile: FORCE
	@make -C $(@D) dots
	@mkdir -p $*
	@find $(@D) -name *.dot -exec rsync -t {} $* \;

# find and build all tex files
.PHONY: all_tex
TEX_FILES := $(shell find . -name *.tex)
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
