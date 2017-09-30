# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind ocamlbuild"

export OPAMYES=1
opam switch ${OCAML_VERSION}
eval `opam config env`
opam install ${OPAM_DEPENDS}
make
sudo make install
