(lang dune 3.0)
(name autoprover)

(generate_opam_files true)

(package
 (name autoprover)
 (synopsis "GhostDAG-powered distributed theorem proving with Claude orchestration")
 (description "Combines formal Coq proofs with Claude AI to generate reliable software")
 (depends
  ocaml
  dune
  coq
  coq-serapi
  bigarray
  lwt
  zarith
  yojson
  httpaf
  httpaf-lwt-unix))

(using menhir 2.1)