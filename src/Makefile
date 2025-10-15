#####  -*- Makefile -*-

DIR = src

SRC = rellens_types.ml print.ml rellens.ml rellens_test.ml rellens_test_util.ml .ocamlinit .camldebug

lib: rellens_types.cmo print.cmo rellens.cmo rellens_test_util.cmo

#OCAMLC = ocamlc -g
OCAMLC = ocamlc

all: lib rellens.pdf

rellens.tex: macro.tex rellens_types.ml rellens.ml
	ocamlweb -noweb rellens_types.ml rellens.ml  > $@


$(DIR).zip: $(SRC) rellens.pdf
	pushd  .. ; ls $(DIR) ;	zip $@ $(addprefix $(DIR)/, $?)

rellens_types.cmo rellens_types.cmi: rellens_types.ml
	$(OCAMLC) -c rellens_types.ml

print.cmi print.cmo: print.ml rellens_types.cmi
	$(OCAMLC) -c print.ml

rellens.cmo: rellens.ml rellens_types.cmi print.cmi
	$(OCAMLC) -c rellens.ml

rellens_test_util.cmo: rellens.cmo rellens_types.cmi print.cmi rellens_test_util.ml
	$(OCAMLC) -c rellens_test_util.ml

rellens_test.cmo: rellens_types.cmi print.cmi rellens.cmi rellens_test_util.cmi rellens_test.ml
	$(OCAMLC) -c rellens_test.ml

rellens_test: lib rellens_test.cmo
	$(OCAMLC) rellens_types.cmo print.cmo rellens.cmo rellens_test_util.cmo rellens_test.cmo -o $@

# %.dvi: %.tex
# 	latex -synctex=1 $<
# 	latex -synctex=1 $<

rellens.dvi: rellens.tex
	latex -synctex=1 $<
	latex -synctex=1 $<

%.pdf: %.dvi
	dvipdfmx $<

rellens.pdf: rellens.dvi
	dvipdfmx $<

.PHONY: all clean

clean:
	rm -f *.cmi *.cmo *.aux *.dvi *.log



