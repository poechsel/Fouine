all:
	ocamlbuild -yaccflag -v -lib unix src/main.native; 
byte:
	ocamlbuild -yaccflag -v main.byte
clean:
	ocamlbuild -clean


