all: toplevel

toplevel: clean
	ocamlfind ocamlc -package ocamlgraph -linkpkg -c dualgraph.ml
	ocamlfind ocamlmktop -package ocamlgraph -linkpkg dualgraph.cmo test.ml -o locaml

clean:
	rm -f *.cmo *.cmi locaml
