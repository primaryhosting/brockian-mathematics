import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma exists_belyiPt (μ : ℚ) (h0 : 0 < μ) (h1 : μ < 1) : ∃ a b : ℕ, belyiPt a b = μ := by
  have hd : (0 : ℚ) < (μ.den : ℚ) := by exact_mod_cast μ.pos
  have hnum : 0 < μ.num := Rat.num_pos.mpr h0
  have hkey : (μ.num : ℚ) = μ * (μ.den : ℚ) := (div_eq_iff (ne_of_gt hd)).mp (Rat.num_div_den μ)
  have hlt : (μ.num : ℚ) < (μ.den : ℚ) := by rw [hkey]; nlinarith
  have hltZ : μ.num < (μ.den : ℤ) := by exact_mod_cast hlt
  set n : ℕ := μ.num.toNat with hn
  have hnnum : (n : ℤ) = μ.num := Int.toNat_of_nonneg hnum.le
  have hn1 : 1 ≤ n := by omega
  have hnd : n + 1 ≤ μ.den := by omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, n = a + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, μ.den = a + b + 2 := ⟨μ.den - n - 1, by omega⟩
  refine ⟨a, b, ?_⟩
  unfold belyiPt
  have e1 : ((a : ℚ) + 1) = (μ.num : ℚ) := by rw [← hnnum, ha]; push_cast; ring
  have e2 : ((a : ℚ) + b + 2) = (μ.den : ℚ) := by rw [hb]; push_cast; ring
  rw [e1, e2, Rat.num_div_den]

/-! ## Step 1 : mapping a finite set of rationals into `{0,1}` -/

