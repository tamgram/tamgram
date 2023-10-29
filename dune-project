(lang dune 2.9)
(using menhir 2.1)

(license "MIT")

(generate_opam_files true)

(name tamgram)

(package
  (name tamgram)
  (synopsis "Frontend to Tamarin prover")
  (description "
"
)
  (depends 
    (ocaml (>= "4.08.1"))
    (bisect_ppx (and :dev (>= "2.5.0")))
    dune
    cmdliner
    (containers (>= "3.6"))
    (angstrom (>= "0.15.0"))
    oseq
    menhir
    fmt
    ANSITerminal
  )
)
