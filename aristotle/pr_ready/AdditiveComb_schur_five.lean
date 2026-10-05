/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Statement: Schur instance: for every function f : Fin 5 -> Bool (a 2-colouring of {1,2,3,4,5}), there exist x y z in {1,..,5} with x + y = z and f x = f y = f z (a monochromatic Schur triple). This is the S(2) < 5 case. Prove by finite case analysis / decide.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace AdditiveComb

/-- **Schur instance `S(2) < 5`.**
Every 2-colouring `f` of `{1, 2, 3, 4, 5}` (encoded as `f : Fin 5 → Bool`, where the index
`i : Fin 5` stands for the number `i + 1`) contains a monochromatic Schur triple: numbers
`x, y, z ∈ {1, …, 5}` with `x + y = z` and `f x = f y = f z`. -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      ((x : ℕ) + 1) + ((y : ℕ) + 1) = ((z : ℕ) + 1) ∧ f x = f y ∧ f y = f z := by
  revert f
  decide

end AdditiveComb

