all:
	ocamlbuild -yaccflag -v -lib unix main.native; 
byte:
	ocamlbuild -yaccflag -v main.byte
clean:
	ocamlbuild -clean


