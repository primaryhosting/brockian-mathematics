import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma bchL_eq_bchR (hc : c = a * b - b * a) (hac : Commute a c) (hbc : Commute b c) (N : ℕ) :
    bchL a b N = bchR c (a + b) N := by
  have hcd : Commute c (a + b) := (hac.add_left hbc).symm
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [bchL_zero, bchR_zero]
    | 1 => rw [bchL_one, bchR_one]
    | (n + 2) =>
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      refine smul_left_cancel_rat (k := ((n + 2 : ℕ) : ℚ)) (by positivity) ?_
      rw [bchL_rec hc hac, bchR_rec hcd, h1, h2]

/-- If `a ^ K = 0 = b ^ K`, then all homogeneous components of degree `≥ 2K` vanish. -/
