/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

theorem not_arrows_eight : ¬ Arrows 8 3 4 := by
  intro h
  rcases h wagner with hA | hB
  · exact wagner_no_triangle hA
  · exact wagner_no_indep_four hB

/-! ### The Ramsey number -/

/-- **R(3,4) = 9.** -/
