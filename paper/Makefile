Paper.pdf : Paper.tex Paper.bbl
	pdflatex Paper.tex

Paper.tex : Paper.lhs
	lhs2TeX Paper.lhs > Paper.tex

Paper.bbl : Paper.lhs Paper.bib
	touch Paper.aux
	bibtex Paper
