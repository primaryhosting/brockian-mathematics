import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
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

namespace Chem

open Matrix

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₆`, i.e. the Hückel matrix of
benzene in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`. -/
noncomputable def C6adj : Matrix (Fin 6) (Fin 6) ℝ :=
  (SimpleGraph.cycleGraph 6).adjMatrix ℝ

/-- Explicit entries of the adjacency matrix of `C₆`. -/
lemma C6adj_eq :
    C6adj = Matrix.of ![![0, 1, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0],
      ![0, 0, 1, 0, 1, 0], ![0, 0, 0, 1, 0, 1], ![1, 0, 0, 0, 1, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj, Fin.ext_iff] <;> decide

/-- The square of the adjacency matrix of `C₆`. -/
noncomputable def C6sq : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![2, 0, 1, 0, 1, 0], ![0, 2, 0, 1, 0, 1], ![1, 0, 2, 0, 1, 0],
    ![0, 1, 0, 2, 0, 1], ![1, 0, 1, 0, 2, 0], ![0, 1, 0, 1, 0, 2]]

lemma C6adj_mul_self : C6adj * C6adj = C6sq := by
  rw [C6adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6sq, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

lemma C6sq_mul_self :
    C6sq * C6sq = (5 : ℝ) • C6sq - (4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6sq, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- Every eigenvalue of the adjacency matrix of `C₆` is a root of `X⁴ - 5X² + 4`. -/
lemma C6_eigenvalue_root {mu : ℝ} {v : Fin 6 → ℝ} (hv : v ≠ 0) (h : C6adj *ᵥ v = mu • v) :
    mu ^ 4 - 5 * mu ^ 2 + 4 = 0 := by
  have h2 : C6sq *ᵥ v = mu ^ 2 • v := by
    rw [← C6adj_mul_self, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]
    ring_nf
  have h4 : (C6sq * C6sq) *ᵥ v = mu ^ 4 • v := by
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  rw [C6sq_mul_self] at h4
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h2, Matrix.one_mulVec,
    smul_smul] at h4
  have hz : (mu ^ 4 - 5 * mu ^ 2 + 4) • v = 0 := by
    linear_combination (norm := module) -h4
  rcases smul_eq_zero.mp hz with h' | h'
  · exact h'
  · exact absurd h' hv

/-- The eigenvalue set of the adjacency matrix of `C₆` is contained in `{2, 1, -1, -2}`. -/
lemma C6_spectrum_subset {mu : ℝ} {v : Fin 6 → ℝ} (hv : v ≠ 0) (h : C6adj *ᵥ v = mu • v) :
    mu = 2 ∨ mu = 1 ∨ mu = -1 ∨ mu = -2 := by
  have hp := C6_eigenvalue_root hv h
  have hfac : (mu - 2) * (mu - 1) * (mu + 1) * (mu + 2) = 0 := by linarith [hp, sq_nonneg mu]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

lemma C6_eigen_two : C6adj *ᵥ ![1, 1, 1, 1, 1, 1] = (2 : ℝ) • ![1, 1, 1, 1, 1, 1] := by
  rw [C6adj_eq]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

lemma C6_eigen_negtwo : C6adj *ᵥ ![1, -1, 1, -1, 1, -1] = (-2 : ℝ) • ![1, -1, 1, -1, 1, -1] := by
  rw [C6adj_eq]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

lemma C6_eigen_one : C6adj *ᵥ ![1, 1, 0, -1, -1, 0] = (1 : ℝ) • ![1, 1, 0, -1, -1, 0] := by
  rw [C6adj_eq]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]

lemma C6_eigen_negone : C6adj *ᵥ ![1, -1, 0, 1, -1, 0] = (-1 : ℝ) • ![1, -1, 0, 1, -1, 0] := by
  rw [C6adj_eq]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]

lemma vec_ne_zero_of_apply {v : Fin 6 → ℝ} {i : Fin 6} (h : v i ≠ 0) : v ≠ 0 := by
  intro hv
  exact h (by simp [hv])

/-- The values `2 cos (2πk/6)` for `k = 0, …, 5` are exactly `{2, 1, -1, -2}`. -/
lemma C6_cos_values :
    (fun k : ℕ => 2 * Real.cos (2 * Real.pi * k / 6)) '' ((Finset.range 6 : Finset ℕ) : Set ℕ)
      = ({2, 1, -1, -2} : Set ℝ) := by
  have hset : ((Finset.range 6 : Finset ℕ) : Set ℕ) = {0, 1, 2, 3, 4, 5} := by
    ext n; simp; omega
  have h0 : 2 * Real.cos (2 * Real.pi * (0 : ℕ) / 6) = 2 := by norm_num
  have h1 : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 6) = 1 := by
    have h : 2 * Real.pi * ((1 : ℕ) : ℝ) / 6 = Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_pi_div_three]; norm_num
  have h2 : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 6) = -1 := by
    have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 6 = Real.pi - Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have h3 : 2 * Real.cos (2 * Real.pi * (3 : ℕ) / 6) = -2 := by
    have h : 2 * Real.pi * ((3 : ℕ) : ℝ) / 6 = Real.pi := by push_cast; ring
    rw [h, Real.cos_pi]; norm_num
  have h4 : 2 * Real.cos (2 * Real.pi * (4 : ℕ) / 6) = -1 := by
    have h : 2 * Real.pi * ((4 : ℕ) : ℝ) / 6 = Real.pi + Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]; ring
  have h5 : 2 * Real.cos (2 * Real.pi * (5 : ℕ) / 6) = 1 := by
    have h : 2 * Real.pi * ((5 : ℕ) : ℝ) / 6 = 2 * Real.pi - Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_two_pi_sub, Real.cos_pi_div_three]; norm_num
  rw [hset]
  simp only [Set.image_insert_eq, Set.image_singleton, h0, h1, h2, h3, h4, h5]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **Hückel theory for benzene (C₆H₆).**
The eigenvalues of the adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene
with `α = 0`, `β = 1`) are exactly the numbers `2 cos (2πk/6)` for `k = 0, 1, …, 5`, namely
`2, 1, 1, -1, -1, -2`. -/
theorem huckel_C6 :
    {mu : ℝ | ∃ v : Fin 6 → ℝ, v ≠ 0 ∧ C6adj *ᵥ v = mu • v}
      = (fun k : ℕ => 2 * Real.cos (2 * Real.pi * k / 6)) ''
          ((Finset.range 6 : Finset ℕ) : Set ℕ) := by
  rw [C6_cos_values]
  ext mu
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact C6_spectrum_subset hv h
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨![1, 1, 1, 1, 1, 1], vec_ne_zero_of_apply (i := 0) (by norm_num), C6_eigen_two⟩
    · exact ⟨![1, 1, 0, -1, -1, 0], vec_ne_zero_of_apply (i := 0) (by norm_num), C6_eigen_one⟩
    · exact ⟨![1, -1, 0, 1, -1, 0], vec_ne_zero_of_apply (i := 0) (by norm_num), C6_eigen_negone⟩
    · exact ⟨![1, -1, 1, -1, 1, -1], vec_ne_zero_of_apply (i := 0) (by norm_num), C6_eigen_negtwo⟩

end Chem

