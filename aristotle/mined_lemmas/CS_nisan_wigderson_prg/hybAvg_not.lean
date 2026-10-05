import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
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

set_option grind.warning false

namespace CS

open Finset

variable {n m : ℕ}

/-- The real value of a boolean: `1` for `true`, `0` for `false`. -/

lemma hybAvg_not (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) (k : ℕ) :
    hybAvg f (fun w => !T w) k = 1 - hybAvg f T k := by
  have h : ∀ b : Bool, bval (!b) = 1 - bval b := by intro b; cases b <;> simp [bval]
  simp only [hybAvg, h]
  rw [eq_sub_iff_add_eq, ← add_div, ← Finset.sum_add_distrib]
  have key : ∀ x : Fin n → Bool,
      (∑ u : Fin m → Bool, (1 - bval (T (hyb f k x u))))
        + ∑ u : Fin m → Bool, bval (T (hyb f k x u)) = 2 ^ m := by
    intro x
    rw [Finset.sum_sub_distrib]
    simp
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  simp

/-! ### A large gap in the hybrid sequence -/

