all:
	ocamlbuild -use-menhir -lib unix main.native; 
byte:
	ocamlbuild -use-menhir main.byte
clean:
	ocamlbuild -clean


