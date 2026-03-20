(lang dune 3.22)

(name strict_order_solver)

(generate_opam_files true)

(using rocq 0.12)

(homepage "https://github.com/epfl-systemf/StrictOrderSolver")
(authors "Kacper Korban" "Dario Halilovic" "Marcin Wojnarowski")
(maintainers "Marcin Wojnarowski")
(bug_reports "https://github.com/epfl-systemf/StrictOrderSolver/issues")
(license MIT)

(package
 (name strict_order_solver)
 (synopsis "Complete solver for strict orders (transitive and irreflexive relations) for Rocq")
 (depends
  (rocq-core (>= 9.0.0))
  (rocq-stdlib (>= 9.0.0))))
