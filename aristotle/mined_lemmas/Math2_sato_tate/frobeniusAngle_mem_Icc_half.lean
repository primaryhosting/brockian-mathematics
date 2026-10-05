/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma frobeniusAngle_mem_Icc_half {p : ℕ} (hp : 0 < p) (a : ℤ) :
    frobeniusAngle p a ∈ Icc 0 (Real.pi / 2) ↔ 0 ≤ a := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  rw [frobeniusAngle, mem_Icc]
  constructor
  · rintro ⟨-, h2⟩
    have h3 := Real.arccos_le_pi_div_two.1 h2
    have h4 : (0 : ℝ) ≤ (a : ℝ) := by
      rcases le_or_gt 0 ((a : ℝ)) with h | h
      · exact h
      · exact absurd (div_neg_of_neg_of_pos h (by linarith)) (not_lt.2 h3)
    exact_mod_cast h4
  · intro h
    refine ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 ?_⟩
    have h4 : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    positivity

/-- A concrete consequence of Sato–Tate: the traces of Frobenius are nonnegative for
exactly half of the primes, in the sense of natural density among the primes. -/
