/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Basic notions -/

/-- The real part of the trace of a matrix. -/

lemma exists_spectral_proj {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    ∃ E : Matrix n n 𝕜, E.IsHermitian ∧ E * E = E ∧ rtr E = (posIndex hM : ℝ) ∧
      (-((1 - E) * M * (1 - E))).PosSemidef := by
  classical
  set U : Matrix n n 𝕜 := (hM.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.2
  have hU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2
  have hspec : M = U * diagonal (RCLike.ofReal ∘ hM.eigenvalues) * Uᴴ := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  set mu : n → ℝ := hM.eigenvalues with hmu
  set g : n → ℝ := fun i => if 0 < mu i then 1 else 0 with hg
  refine ⟨U * diagonal (RCLike.ofReal ∘ g) * Uᴴ, conj_diag_herm g, ?_, ?_, ?_⟩
  · have hff : ((RCLike.ofReal ∘ g) * (RCLike.ofReal ∘ g) : n → 𝕜) = RCLike.ofReal ∘ g := by
      funext i
      by_cases h : 0 < mu i <;> simp [hg, h]
    rw [conj_diag_mul hU, hff]
  · rw [rtr, conj_diag_trace hU,
      show (∑ i, (RCLike.ofReal ∘ g) i : 𝕜) = ((∑ i, g i : ℝ) : 𝕜) by push_cast; rfl,
      RCLike.ofReal_re, hg, posIndex, Finset.sum_boole]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hmu]
  · have hone : (1 : Matrix n n 𝕜) = U * diagonal (fun _ => (1 : 𝕜)) * Uᴴ := by
      simp [Matrix.diagonal_one, hU']
    have hsub : ((fun _ => (1 : 𝕜)) - RCLike.ofReal ∘ g : n → 𝕜)
        = RCLike.ofReal ∘ (fun i => 1 - g i) := by
      funext i; simp
    have hcompl : (1 : Matrix n n 𝕜) - U * diagonal (RCLike.ofReal ∘ g) * Uᴴ
        = U * diagonal (RCLike.ofReal ∘ (fun i => 1 - g i)) * Uᴴ := by
      rw [hone, conj_diag_sub, hsub]
    set k : n → ℝ := fun i => (1 - g i) * mu i * (1 - g i) with hk
    have hprod : ((RCLike.ofReal ∘ (fun i => 1 - g i)) * (RCLike.ofReal ∘ mu) *
        (RCLike.ofReal ∘ (fun i => 1 - g i)) : n → 𝕜) = RCLike.ofReal ∘ k := by
      funext i
      simp [hk]
    rw [hcompl, hspec, conj_diag_mul hU, conj_diag_mul hU, hprod, conj_diag_neg]
    have hd : (diagonal (-(RCLike.ofReal ∘ k)) : Matrix n n 𝕜).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      have he : (-(RCLike.ofReal ∘ k) : n → 𝕜) i = ((-(k i) : ℝ) : 𝕜) := by simp
      rw [he]
      refine RCLike.ofReal_nonneg.mpr ?_
      by_cases h : 0 < mu i
      · simp [hk, hg, h]
      · have h' := not_lt.mp h
        simp only [hk, hg, h, if_false, sub_zero, one_mul, mul_one]
        linarith
    exact hd.mul_mul_conjTranspose_same U

/-- For a positive semidefinite matrix, the positive index of inertia is the rank. -/
