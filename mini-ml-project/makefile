all: evaluation expr miniml test_simple tests

evaluation: evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte

expr: expr.ml
	ocamlbuild -use-ocamlfind expr.byte

miniml: miniml.ml
	ocamlbuild -use-ocamlfind miniml.byte

test_simple: test_simple.ml
	ocamlbuild -use-ocamlfind test_simple.byte

tests: tests.ml
	ocamlbuild -use-ocamlfind tests.byte

clean:
	rm -rf _build *.byte
