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

lemma sum_maskMerge (S : Finset (Fin n)) (g : (Fin n → Bool) → ℝ) :
    ∑ x : Fin n → Bool, ∑ z : Fin n → Bool, g (maskMerge S x z)
      = 2 ^ n * ∑ x : Fin n → Bool, g x := by
  have hinv : Function.Involutive (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      (maskMerge S p.1 p.2, maskMerge S p.2 p.1)) := by
    intro p
    ext1 <;> · funext j; by_cases h : j ∈ S <;> simp [maskMerge, h]
  have h1 : ∑ p : (Fin n → Bool) × (Fin n → Bool), g (maskMerge S p.1 p.2)
      = ∑ p : (Fin n → Bool) × (Fin n → Bool), g p.1 :=
    Fintype.sum_equiv (hinv.toPerm _) _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h1
  rw [h1]
  simp [Finset.mul_sum, mul_comm]

