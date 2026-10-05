/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

/-- The number of inputs on which `f` takes the value `true`. -/

lemma djAmp_zero_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f (fun _ => false) = ((2 ^ n : ℝ) - 2 * trueCount f) / 2 ^ n := by
  have hsum : (∑ x : Fin n → Bool, (-1 : ℝ) ^ ((f x).toNat + parityDot x (fun _ => false)))
      = (2 ^ n : ℝ) - 2 * trueCount f := by
    have h1 : ∀ x : Fin n → Bool,
        (-1 : ℝ) ^ ((f x).toNat + parityDot x (fun _ => false))
          = if f x = true then (-1 : ℝ) else 1 := by
      intro x
      rcases hx : f x with _ | _ <;> simp [parityDot_zero]
    rw [Finset.sum_congr rfl (fun x _ => h1 x)]
    rw [Finset.sum_ite]
    have hT : (Finset.univ.filter fun x : Fin n → Bool => f x = true).card = trueCount f := rfl
    have hF : (Finset.univ.filter fun x : Fin n → Bool => ¬ (f x = true)).card
        = 2 ^ n - trueCount f := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Bool))) (p := fun x => f x = true)
      rw [card_domain] at this
      omega
    have hle : trueCount f ≤ 2 ^ n := trueCount_le f
    simp only [Finset.sum_const, nsmul_eq_mul, hT, hF]
    have : ((2 ^ n - trueCount f : ℕ) : ℝ) = (2 ^ n : ℝ) - trueCount f := by
      push_cast [Nat.cast_sub hle]
      ring
    rw [this]
    ring
  rw [djAmp, hsum]

