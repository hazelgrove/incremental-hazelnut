LATEXMK ?= latexmk

.PHONY: all
all : formalism.pdf

.PHONY: formalism.pdf
formalism.pdf : formalism/formalism.tex
	cd formalism && $(LATEXMK) formalism.tex
	cp formalism/build/formalism.pdf formalism.pdf

.PHONY : clean
clean :
	rm -rf formalism/build
	rm -f *.pdf
