Paper.pdf : Paper.tex Paper.bbl
	pdflatex Paper.tex && ( grep -s "Rerun to get" Paper.log && pdflatex Paper.tex || true )

Paper.tex : Paper.lhs
	lhs2TeX Paper.lhs > Paper.tex

Paper.aux : Paper.tex
	pdflatex Paper.tex

Paper.bbl : Paper.aux Paper.bib
	bibtex Paper
