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

lemma exists_ge_unifAvg {α : Type*} [Fintype α] [Nonempty α] (g : α → ℝ) :
    ∃ a, unifAvg g ≤ g a := by
  have hcard : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ _a : α, unifAvg g ≤ ∑ a, g a := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unifAvg,
      mul_div_cancel₀ _ (ne_of_gt hcard)]
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨a, ha⟩

