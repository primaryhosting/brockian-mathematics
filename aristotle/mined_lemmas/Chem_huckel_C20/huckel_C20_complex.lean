import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma huckel_C20_complex (μ : ℂ) :
    (∃ v : Fin 20 → ℂ, v ≠ 0 ∧ AC *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 20 ∧ μ = w ^ k + w ^ (20 - k) := by
  constructor
  · rintro ⟨v, hv, h⟩
    have h1 : (pt.eval μ) • v = 0 := by
      rw [← aeval_mulVec h pt, aeval_AC_pt, Matrix.zero_mulVec]
    have h2 : pt.eval μ = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hv
    rw [pt, eval_prod] at h2
    obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.mp h2
    refine ⟨k, Finset.mem_range.mp hk, ?_⟩
    simp only [eval_sub, eval_X, eval_C] at hk0
    exact sub_eq_zero.mp hk0
  · rintro ⟨k, hk, rfl⟩
    exact ⟨fvec k, fvec_ne_zero k, AC_mulVec_fvec k (by omega)⟩

