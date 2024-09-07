(lang dune 3.15)

(name nbe)

(using menhir 2.0)

(generate_opam_files true)

(source
 (github glyh/nbe))

(authors "Yihang Liu")

(maintainers "Yihang Liu")

(license GPL-3.0-or-later)

(documentation https://github.com/glyh/nbe)

(package
 (name nbe)
 (synopsis "Elaboration Zoo implemented in OCaml")
 (description "Elaboration Zoo implemented in OCaml")
 (depends
   ocaml
   dune
   menhir
   (nice_parser (>= 1.0.0))
   (linenoise (>= 1.5.1))
   (ppx_inline_test (>= 0.14.1))
   (fmlib_std (>= 0.5.9)))
 (tags
  (topics compiler)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
