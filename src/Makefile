#####  -*- Makefile -*-

DIR = src

SRC = rellens_types.ml print.ml rellens.ml rellens_test.ml rellens_test_util.ml .ocamlinit .camldebug

all: rellens_types.cmo print.cmo rellens.cmo rellens_test_util.cmo rellens.pdf

rellens.tex: macro.tex rellens_types.ml rellens.ml
	ocamlweb -noweb rellens_types.ml rellens.ml  > $@


$(DIR).zip: $(SRC) rellens.pdf
	pushd  .. ; ls $(DIR) ;	zip $@ $(addprefix $(DIR)/, $?)

rellens_types.cmo rellens_types.cmi: rellens_types.ml
	ocamlc -c rellens_types.ml

print.cmi print.cmo: print.ml rellens_types.cmi
	ocamlc -c print.ml

rellens.cmo: rellens.ml rellens_types.cmi print.cmi
	ocamlc -c rellens.ml

rellens_test_util.cmo: rellens.cmo rellens_types.cmi print.cmi rellens_test_util.ml
	ocamlc -c rellens_test_util.ml

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



