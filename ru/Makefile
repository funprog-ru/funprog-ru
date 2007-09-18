PDFLATEX = pdflatex

all: all.pdf slides

all.pdf: all.tex preface.tex plan.tex intro.tex lamb.tex prog.tex types.tex ml.tex fml.tex	\
	 proving.tex effect.tex examples.tex all.bbl
	pdflatex all
	while grep 'Label(s) may have changed' all.log > /dev/null 2>&1 ; do \
		$(PDFLATEX) all ; \
	done 

all.bbl: all.bib
				 $(PDFLATEX) all
				 bibtex all

clean:; rm -f *.aux *.log all.bbl *.dvi all.blg *.toc all.pdf l[0-9]*.pdf 

slides: l1.pdf l2.pdf l3.pdf l4.pdf l5.pdf l6.pdf l7.pdf l8.pdf l9.pdf l10.pdf l11.pdf l12.pdf

l1.pdf: l1.tex fp-slides.cls
			 pdflatex l1.tex

l2.pdf: l2.tex fp-slides.cls
			 pdflatex l2.tex

l3.pdf: l3.tex fp-slides.cls
			 pdflatex l3.tex

l4.pdf: l4.tex fp-slides.cls
			 pdflatex l4.tex

l5.pdf: l5.tex fp-slides.cls
			 pdflatex l5.tex

l6.pdf: l6.tex fp-slides.cls
			 pdflatex l6.tex

l7.pdf: l7.tex fp-slides.cls
			 pdflatex l7.tex

l8.pdf: l8.tex fp-slides.cls
			 pdflatex l8.tex

l9.pdf: l9.tex fp-slides.cls
			 pdflatex l9.tex

l10.pdf: l10.tex fp-slides.cls
			 pdflatex l10.tex

l11.pdf: l11.tex fp-slides.cls
			 pdflatex l11.tex

l12.pdf: l12.tex fp-slides.cls
			 pdflatex l12.tex
