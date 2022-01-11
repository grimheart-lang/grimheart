(lang dune 2.9)

(name "sulfur")
(version "0.1.0")
(maintainers "Justin Garcia")
(authors "Justin Garcia")
(license "BSD-3-Clause")
(homepage "https://github.com/sjpgarcia/sulfur")
(bug_reports "https://github.com/sjpgarcia/sulfur/issues")

(using menhir 2.1)

(generate_opam_files true)

(package
 (name "sulfur")
 (synopsis "Functional programming language with rich type inference")
 (depends
  ("core_kernel"
   (>= "v0.14.2"))
  ("ppx_deriving"
   (>= "5.2.1"))
  ("dolog"
   (>= "6.0.0"))))

