/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma exists_range_proj {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) :
    ∃ R : Matrix (Fin d) (Fin d) ℂ, R.IsHermitian ∧ R * R = R ∧ P * R = P ∧
      (1 - R).PosSemidef ∧ rtrace R = (P.rank : ℝ) := by
  obtain ⟨V, hV1, hV2, hspec⟩ := exists_spectral hP.1
  set p : Fin d → ℝ := hP.1.eigenvalues with hp
  set e : Fin d → ℝ := fun i => if p i ≠ 0 then 1 else 0 with he
  have hstar : (diagonal (fun i => ((e i : ℝ) : ℂ)))ᴴ = diagonal (fun i => ((e i : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hee : (fun i => ((e i : ℝ) : ℂ) * ((e i : ℝ) : ℂ)) = fun i => ((e i : ℝ) : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul]
    congr 1
    by_cases h : p i = 0 <;> simp [he, h]
  have hpe : (fun i => ((p i : ℝ) : ℂ) * ((e i : ℝ) : ℂ)) = fun i => ((p i : ℝ) : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul]
    congr 1
    by_cases h : p i = 0 <;> simp [he, h]
  refine ⟨V * diagonal (fun i => ((e i : ℝ) : ℂ)) * Vᴴ, ?_, ?_, ?_, ?_, ?_⟩
  · show (V * diagonal (fun i => ((e i : ℝ) : ℂ)) * Vᴴ)ᴴ = _
    rw [conj_conjTranspose, hstar]
  · rw [conj_mul hV1, Matrix.diagonal_mul_diagonal, hee]
  · rw [hspec, conj_mul hV1, Matrix.diagonal_mul_diagonal, hpe]
  · have hone : (1 : Matrix (Fin d) (Fin d) ℂ) = V * (1 : Matrix (Fin d) (Fin d) ℂ) * Vᴴ := by
      rw [Matrix.mul_one, hV2]
    have hsub : (1 : Matrix (Fin d) (Fin d) ℂ) - V * diagonal (fun i => ((e i : ℝ) : ℂ)) * Vᴴ
        = V * diagonal (fun i => (((1 - e i : ℝ)) : ℂ)) * Vᴴ := by
      have hdd : diagonal (fun i => (((1 - e i : ℝ)) : ℂ))
          = (1 : Matrix (Fin d) (Fin d) ℂ) - diagonal (fun i => ((e i : ℝ) : ℂ)) := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
        congr 1
        funext i
        simp
      rw [hdd, Matrix.mul_sub, Matrix.sub_mul, ← hone]
    rw [hsub]
    refine conj_posSemidef (diagonal_posSemidef_of_nonneg ?_)
    intro i
    by_cases h : p i = 0 <;> simp [he, h]
  · rw [conj_rtrace hV1, rtrace_diagonal, hP.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
      ← hp]
    have hcongr : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        e i = if ¬ p i = 0 then (1 : ℝ) else 0 := by
      intro i _
      by_cases h : p i = 0 <;> simp [he, h]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite, Finset.sum_const]
    simp

/-! ### The rank-trace inequality -/

/-- **Rank-trace inequality.** For `P` positive semidefinite with `rank P ≤ r` and `Q`
Hermitian with at most `b` strictly positive eigenvalues, and any `c > 0`,
`c * tr P - (c²/4) r + 2c * tr Q - c² b ≤ ‖P + Q‖_F²`. -/
