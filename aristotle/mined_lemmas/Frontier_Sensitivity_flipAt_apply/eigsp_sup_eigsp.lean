import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma eigsp_sup_eigsp {n : ℕ} (hn : 0 < n) :
    (eigsp (n := n) (Real.sqrt n)) ⊔ (eigsp (n := n) (-Real.sqrt n)) = ⊤ := by
  set s := Real.sqrt n with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs2 : s * s = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  rw [eq_top_iff]
  intro x _
  rw [Submodule.mem_sup]
  refine ⟨(1/(2*s)) • (sgnAdj *ᵥ x + s • x), ?_, (1/(2*s)) • (s • x - sgnAdj *ᵥ x), ?_, ?_⟩
  · rw [mem_eigsp_iff, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      sgnAdj_mulVec_sq, ← hs2]
    match_scalars <;> field_simp
  · rw [mem_eigsp_iff, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
      sgnAdj_mulVec_sq, ← hs2]
    match_scalars <;> field_simp
  · rw [← smul_add]
    have h3 : sgnAdj *ᵥ x + s • x + (s • x - sgnAdj *ᵥ x) = (2*s) • x := by module
    rw [h3, smul_smul]
    field_simp
    exact one_smul _ x

/-- Support subspace of a vertex set: functions vanishing outside `H`. -/
