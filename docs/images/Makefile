TEX_SOURCE:= $(wildcard *.tex)
PDF_OUTPUT:= $(patsubst %.tex,%.pdf,$(TEX_SOURCE))
SVG_OUTPUT:= $(patsubst %.tex,%.svg,$(TEX_SOURCE))

all: $(PDF_OUTPUT) $(SVG_OUTPUT)

%.pdf %.log %.aux: %.tex
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
