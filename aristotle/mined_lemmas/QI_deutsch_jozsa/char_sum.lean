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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/

theorem char_sum (f : Bits n → Bool) :
    ∑ x : Bits n, (if f x then (-1 : ℂ) else 1)
      = (2 : ℂ) ^ n - 2 * ((Finset.univ.filter (fun x : Bits n => f x = true)).card : ℂ) := by
  classical
  have hsplit :
      ∑ x : Bits n, (if f x then (-1 : ℂ) else 1)
        = ∑ x ∈ Finset.univ.filter (fun x : Bits n => f x = true), (-1 : ℂ)
          + ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (f x = true)), (1 : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Bits n => f x = true)]
    congr 1
    · exact Finset.sum_congr rfl (by intro x hx; simp at hx; simp [hx])
    · exact Finset.sum_congr rfl (by intro x hx; simp at hx; simp [hx])
  rw [hsplit]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have hcard :
      (Finset.univ.filter (fun x : Bits n => f x = true)).card
        + (Finset.univ.filter (fun x : Bits n => ¬ (f x = true))).card
        = Fintype.card (Bits n) :=
    Finset.card_filter_add_card_filter_not _
  have hc : Fintype.card (Bits n) = 2 ^ n := by
    simp [Bits]
  rw [hc] at hcard
  have hcast := congrArg (fun m : ℕ => (m : ℂ)) hcard
  push_cast at hcast
  have hnot : ((Finset.univ.filter (fun x : Bits n => ¬ (f x = true))).card : ℂ)
      = (2 : ℂ) ^ n - ((Finset.univ.filter (fun x : Bits n => f x = true)).card : ℂ) := by
    linear_combination hcast
  rw [hnot]
  ring

/-! ### The theorem -/

/-- In the constant case every amplitude other than that of `|0…0⟩` vanishes. -/
