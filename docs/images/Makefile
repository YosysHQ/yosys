TEX_SOURCE:= $(wildcard *.tex)
DOT_LOC:= ../../manual/APPNOTE_011_Design_Investigation
DOT_SOURCE:= $(wildcard $(DOT_LOC)/*.dot)

TEX_PDF:= $(patsubst %.tex,%.pdf,$(TEX_SOURCE))
DOT_PDF:= $(addprefix 011/,$(notdir $(patsubst %.dot,%.pdf,$(DOT_SOURCE))))
SVG_OUTPUT:= $(patsubst %.pdf,%.svg,$(TEX_PDF) $(DOT_PDF))

all: dots tex svg
dots: $(DOT_PDF)
tex: $(TEX_PDF)
svg: $(SVG_OUTPUT)

011/%.pdf: $(DOT_LOC)/%.dot
	dot -Tpdf -o $@ $<

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
	rm -f 011/*.pdf 011/*.svg
