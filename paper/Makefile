# Build the paper with MiKTeX latexmk (or fall back to pdflatex/bibtex).
all: main.pdf

main.pdf: main.tex refs.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	latexmk -C
