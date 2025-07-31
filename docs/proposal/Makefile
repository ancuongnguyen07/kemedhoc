SHELL := /bin/bash

# MAIN=report
# variable `MAIN` is passed during runtime
TEXSRC=$(wildcard *.tex tex/*.tex)
BIBSRC=$(wildcard *.bib)
DIR_BUILD=build
# OPT= --interaction=nonstopmode

all: $(DIR_BUILD)/$(MAIN).pdf

$(DIR_BUILD)/$(MAIN).pdf: $(TEXSRC) $(BIBSRC)
	latexmk -pdf -pdflatex="texfot pdflatex " $(MAIN) -auxdir=$(DIR_BUILD) -outdir=$(DIR_BUILD)

clean:
	rm -rf $(DIR_BUILD)
	rm -f $(MAIN).{aux,bbl,bcf,blg,fdb_latexmk,fls,lof,log,out,run.xml,synctex.gz,toc}
	rm -f *.log
.PHONY: clean all