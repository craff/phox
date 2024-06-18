(lang dune 2.1)
(generate_opam_files)

(authors "Christophe Raffalli")
(maintainers "christophe@raffalli.eu")

(package
 (name phox)
 (description "The PhoX theorem prover")
 (depends unix num camlp5 js_of_ocaml))
