(lang dune 2.9)

(name "grimheart")
(version "0.1.0")
(maintainers "Justin Garcia")
(authors "Justin Garcia")
(license "BSD-3-Clause")
(homepage "https://github.com/grimheart-lang/grimheart")
(bug_reports "https://github.com/grimheart-lang/grimheart/issues")

(using menhir 2.1)

(generate_opam_files true)

(package
 (name "grimheart_ast")
 (synopsis "Core modules for the syntax")
 (depends
  ("core_kernel"
   (>= "v0.14.2"))
  ("ppx_deriving"
   (>= "5.2.1"))))

(package
 (name "grimheart_core")
 (synopsis "Core modules for the language")
 (depends
  ("alcotest"
   (and :with-test (>= "1.5.0")))
  ("bisect_ppx"
   (and :with-test (>= "2.7.0")))
  ("core_kernel"
   (>= "v0.14.2"))
  ("ppx_deriving"
   (>= "5.2.1"))
  ("dolog"
   (>= "6.0.0"))
  ("grimheart_ast"
   (= :version))))
