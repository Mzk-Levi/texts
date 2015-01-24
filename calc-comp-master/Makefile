include makecoq


doc: doc/toc.html

doc/toc.html: $(VOFILES) 
	mkdir -p doc
	coqdoc *.v -d doc -toc --no-index

cleandoc:
	rm -r doc

cleanall: cleandoc clean
