import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

theorem sum_zmod_five (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ x : Fin 5, f x = _
  rw [Fin.sum_univ_five]

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` is `5` when `a = 0` and `0` otherwise. -/
