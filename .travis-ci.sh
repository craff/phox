# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind ocamlbuild"

case "$OCAML_VERSION,$OPAM_VERSION" in
4.02.0,1.2.0) ppa=avsm/ocaml42+opam12 ;;
4.02.0,2.0.0) ppa=avsm/ocaml42+opam20 ;;
4.03.0,1.2.0) ppa=avsm/ocaml43+opam12 ;;
4.03.0,2.0.0) ppa=avsm/ocaml43+opam20 ;;
4.04.0,1.2.0) ppa=avsm/ocaml44+opam12 ;;
4.04.0,2.0.0) ppa=avsm/ocaml44+opam20 ;;
4.05.0,1.2.0) ppa=avsm/ocaml45+opam12 ;;
4.05.0,2.0.0) ppa=avsm/ocaml45+opam20 ;;
*) echo Unknown $OCAML_VERSION,$OPAM_VERSION; exit 1 ;;
esac

echo "yes" | sudo add-apt-repository ppa:$ppa
sudo apt-get update -qq
sudo apt-get install -qq ocaml opam
export OPAMYES=1
opam init
opam install ${OPAM_DEPENDS}
eval `opam config env`
make
sudo make install
