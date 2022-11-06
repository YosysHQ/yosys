all: dots tex svg

TEX_SOURCE:= $(wildcard *.tex)
DOT_LOC:= ../../manual/APPNOTE_011_Design_Investigation
DOT_SOURCE:= $(wildcard $(DOT_LOC)/*.dot)

TEX_SOURCE+= 011/example_out.tex
011/example_out.pdf: 011/example_00.pdf 011/example_01.pdf 011/example_02.pdf
TEX_SOURCE+= 011/select_prod.tex
011/select_prod.pdf: 011/sumprod_02.pdf 011/sumprod_03.pdf 011/sumprod_04.pdf 011/sumprod_05.pdf
TEX_SOURCE+= 011/splitnets_libfile.tex
011/splitnets_libfile.pdf: 011/cmos_00.pdf 011/cmos_01.pdf
TEX_SOURCE+= 011/submod_dots.tex
011/submod_dots.pdf: 011/submod_00.pdf 011/submod_01.pdf 011/submod_02.pdf 011/submod_03.pdf

TEX_PDF:= $(patsubst %.tex,%.pdf,$(TEX_SOURCE))
DOT_PDF:= $(addprefix 011/,$(notdir $(patsubst %.dot,%.pdf,$(DOT_SOURCE))))
SVG_OUTPUT:= $(patsubst %.pdf,%.svg,$(TEX_PDF) $(DOT_PDF))

dots: $(DOT_PDF)
tex: $(TEX_PDF)
svg: $(SVG_OUTPUT)

011/%.pdf: $(DOT_LOC)/%.dot
	dot -Tpdf -o $@ $<

011/%.pdf: 011/%.tex
	cd 011 && pdflatex $(<F) --interaction=nonstopmode

%.pdf: %.tex
	pdflatex $< --interaction=nonstopmode

%.svg: %.pdf
	pdf2svg $< $@

.PHONY: clean tidy
tidy:
	rm -f *.log
	rm -f *.aux
clean: tidy
	rm -f *.pdf
	rm -f *.svg
	rm -f 011/*.pdf 011/*.svg 011/*.log 011/*.aux
