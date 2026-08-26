# CPP 2027 paper. acmart.cls / ACM-Reference-Format.bst are vendored (MacTeX lacks them).
# latexmk drives pdflatex + bibtex to a fixed point.
all:
	latexmk -pdf -interaction=nonstopmode main.tex

clean:
	latexmk -C
	rm -f main.bbl

.PHONY: all clean
