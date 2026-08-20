import Mathlib

/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace AdditiveComb

/-- **Schur's theorem, the instance `S(2) < 5`.**

For every 2-colouring `f` of `{1, 2, 3, 4, 5}` (encoded as `f : Fin 5 → Bool`, where the
index `i : Fin 5` stands for the integer `i + 1`) there is a monochromatic Schur triple:
elements `x`, `y`, `z` of `{1, …, 5}` with `x + y = z` and `f x = f y = f z`. -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      ((x : ℕ) + 1) + ((y : ℕ) + 1) = ((z : ℕ) + 1) ∧ f x = f y ∧ f y = f z := by
  revert f
  decide +kernel

/-- Sharpness of `schur_five`: the analogous statement for `{1, 2, 3, 4}` is false, i.e. there is a
2-colouring of `{1,2,3,4}` with no monochromatic Schur triple.  Hence the Schur number `S(2)`
equals `4`. -/
theorem not_schur_four :
    ¬ ∀ f : Fin 4 → Bool, ∃ x y z : Fin 4,
      ((x : ℕ) + 1) + ((y : ℕ) + 1) = ((z : ℕ) + 1) ∧ f x = f y ∧ f y = f z := by
  decide +kernel

end AdditiveComb

