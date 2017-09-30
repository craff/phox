# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind ocamlbuild"

sudo apt-get install -qq opam
export OPAMYES=1
opam init
opam switch ${OCAML_VERSION}
eval `opam config env`
opam install ${OPAM_DEPENDS}
make
sudo make install
