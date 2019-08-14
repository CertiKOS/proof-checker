CC=latexmk
FLAGS=-pdf
CLFLAGS=-C -pdf
TARGS=checker.pdf
LIBS=checker.sty

all: $(TARGS)
	@echo "Done."

$(TARGS): %.pdf: %.tex $(LIBS)
	$(CC) $(FLAGS) $<

.PHONY: clean
clean:
	$(CC) $(CLFLAGS) $(TARGS)
