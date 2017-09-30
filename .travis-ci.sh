# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind ocamlbuild"

opam install ${OPAM_DEPENDS}
make
sudo make install
