.PHONY: logistics
logistics: logistics.tex
	latexmk -synctex=1 -pdf -shell-escape logistics.tex

hw5w: hw5w.tex
	latexmk -synctex=1 -pdf -shell-escape hw5w.tex

clean:
	@rm -rf \
	  *.aux \
	  \#*\# \
	  *.log \
	  *.bbl \
	  *.out \
	  *~ \
	  *.pdf \
	  *.dvi \
	  *.synctex.gz \
	  *.blg \
	  *.toc \
	  *.lot \
	  *.fls \
	  *.rip \
	  *.fdb_latexmk \
	  *.xcp \
	  *.xoj \
	  *.lof \
	  *.brf \
	  *.diagnose \
	  *.kaux \
	  .\#*.tex \
	  *.nav \
	  *.snm
