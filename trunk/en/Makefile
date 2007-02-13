all.dvi: *.tex all.bib; ./lmake all all.bib *.tex

clean:; rm -f all.ps all.aux all.log all.bbl all.dvi all.blg all.toc

chapters: chapter0.dvi chapter1.dvi chapter2.dvi chapter3.dvi   \
          chapter4.dvi chapter5.dvi chapter6.dvi chapter7.dvi   \
          chapter8.dvi chapter9.dvi chaptera.dvi ;

chapter0.dvi: all.dvi ; dviselect -i all.dvi -o chapter0.dvi =1-8
chapter1.dvi: all.dvi ; dviselect -i all.dvi -o chapter1.dvi =9-14
chapter2.dvi: all.dvi ; dviselect -i all.dvi -o chapter2.dvi =15-31
chapter3.dvi: all.dvi ; dviselect -i all.dvi -o chapter3.dvi 24-37
chapter4.dvi: all.dvi ; dviselect -i all.dvi -o chapter4.dvi 38-49
chapter5.dvi: all.dvi ; dviselect -i all.dvi -o chapter5.dvi 50-62
chapter6.dvi: all.dvi ; dviselect -i all.dvi -o chapter6.dvi 63-80
chapter7.dvi: all.dvi ; dviselect -i all.dvi -o chapter7.dvi 81-93
chapter8.dvi: all.dvi ; dviselect -i all.dvi -o chapter8.dvi 94-108
chapter9.dvi: all.dvi ; dviselect -i all.dvi -o chapter9.dvi 109-155
chaptera.dvi: all.dvi ; dviselect -i all.dvi -o chaptera.dvi 156-160
