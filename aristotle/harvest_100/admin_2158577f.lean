/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required
-- header appears above as a plain comment and again below as a docstring.)

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

noncomputable section

/-! ## The quantum ingredients

We work with two qubits, i.e. with the space of functions `Fin 2 × Fin 2 → ℂ`,
equipped with the standard Hermitian inner product. -/

/-- The standard Hermitian inner product on the two-qubit space. -/
def inner4 (x y : Fin 2 × Fin 2 → ℂ) : ℂ :=
  ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (x p) * y p

/-- `1/√2`, as a complex number. -/
def rt : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma rt_sq : rt * rt = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [rt, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = ((Real.sqrt 2) * (Real.sqrt 2))⁻¹ by ring, h]
  norm_num

lemma conj_rt : (starRingEnd ℂ) rt = rt := by
  simp [rt, ← Complex.ofReal_inv]

/-- The qubit state `|0⟩`. -/
def ket0 : Fin 2 → ℂ := ![1, 0]

/-- The qubit state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
def ketPlus : Fin 2 → ℂ := ![rt, rt]

/-- The two preparations considered by Pusey–Barrett–Rudolph:
`prep false = |0⟩` and `prep true = |+⟩`. -/
def prep : Bool → (Fin 2 → ℂ) := fun b => if b then ketPlus else ket0

/-- Tensor product of two qubit states. -/
def tens (a b : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => a p.1 * b p.2

/-- The four vectors of the PBR entangled measurement basis:

* `ξ₀ = (|01⟩ + |10⟩)/√2`,
* `ξ₁ = (|0-⟩ + |1+⟩)/√2 = (|00⟩ - |01⟩ + |10⟩ + |11⟩)/2`,
* `ξ₂ = (|+1⟩ + |-0⟩)/√2 = (|00⟩ + |01⟩ - |10⟩ + |11⟩)/2`,
* `ξ₃ = (|+-⟩ + |-+⟩)/√2 = (|00⟩ - |11⟩)/√2`. -/
def pbrVec : Fin 4 → (Fin 2 × Fin 2 → ℂ) :=
  ![fun p => !![0, rt; rt, 0] p.1 p.2,
    fun p => !![1/2, -(1/2); 1/2, 1/2] p.1 p.2,
    fun p => !![1/2, 1/2; -(1/2), 1/2] p.1 p.2,
    fun p => !![rt, 0; 0, -rt] p.1 p.2]

/-- The preparation pair whose Born probability for the corresponding PBR
outcome vanishes: outcome `k` is impossible for the preparation `excluded k`. -/
def excluded : Fin 4 → Bool × Bool :=
  ![(false, false), (false, true), (true, false), (true, true)]

/-- The quantum (Born rule) probability of PBR outcome `k` for the product
preparation `prep b₁ ⊗ prep b₂`. -/
def bornProb (k : Fin 4) (b₁ b₂ : Bool) : ℝ :=
  ‖inner4 (pbrVec k) (tens (prep b₁) (prep b₂))‖ ^ 2

lemma inner4_expand (x y : Fin 2 × Fin 2 → ℂ) :
    inner4 x y =
      (starRingEnd ℂ) (x (0,0)) * y (0,0) + (starRingEnd ℂ) (x (0,1)) * y (0,1)
      + ((starRingEnd ℂ) (x (1,0)) * y (1,0) + (starRingEnd ℂ) (x (1,1)) * y (1,1)) := by
  simp [inner4, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **Key quantum fact.** Each PBR outcome has zero Born probability on the
corresponding product preparation: the PBR basis vector `ξ_k` is orthogonal to
`prep b₁ ⊗ prep b₂` where `(b₁, b₂) = excluded k`. -/
theorem bornProb_excluded (k : Fin 4) :
    bornProb k (excluded k).1 (excluded k).2 = 0 := by
  fin_cases k <;>
    simp only [bornProb, excluded, inner4_expand, pbrVec, tens, prep, ket0, ketPlus] <;>
    norm_num [conj_rt]

/-! ### The PBR basis is an orthonormal basis

These facts are not needed for the main theorem, but they certify that the
four response functions of an ontological model really do come from a genuine
projective measurement on the two-qubit space. -/

theorem pbrVec_orthonormal (k j : Fin 4) :
    inner4 (pbrVec k) (pbrVec j) = if k = j then 1 else 0 := by
  fin_cases k <;> fin_cases j <;>
    simp only [inner4_expand, pbrVec, Matrix.cons_val'] <;>
    norm_num [conj_rt, map_ofNat, rt_sq]

/-! ## Ontological models with preparation independence -/

/-- An ontological (hidden variable) model for the two preparations `|0⟩` and
`|+⟩` together with the PBR measurement on two independently prepared systems.

* `mu b` is the probability distribution over the ontic state space `Λ`
  associated with the preparation `prep b`;
* `resp k λ₁ λ₂` is the response function: the probability that the PBR
  measurement performed on the pair of systems with ontic states `λ₁, λ₂`
  yields outcome `k`;
* `born` expresses **preparation independence** (the ontic state of the pair
  is distributed as the product `mu b₁ ⊗ mu b₂`) together with the requirement
  that the model reproduce the quantum (Born rule) statistics. -/
structure OntologicalModel (Λ : Type*) [Fintype Λ] where
  mu : Bool → Λ → ℝ
  mu_nonneg : ∀ b l, 0 ≤ mu b l
  mu_sum_one : ∀ b, ∑ l, mu b l = 1
  resp : Fin 4 → Λ → Λ → ℝ
  resp_nonneg : ∀ k l₁ l₂, 0 ≤ resp k l₁ l₂
  resp_sum_one : ∀ l₁ l₂, ∑ k, resp k l₁ l₂ = 1
  born : ∀ (k : Fin 4) (b₁ b₂ : Bool),
    ∑ l₁, ∑ l₂, mu b₁ l₁ * mu b₂ l₂ * resp k l₁ l₂ = bornProb k b₁ b₂

variable {Λ : Type*} [Fintype Λ]

/-- In any such model, a response function vanishes at any ontic state that
lies in the support of both `mu false` and `mu true`. -/
lemma resp_eq_zero_of_mem_overlap (M : OntologicalModel Λ) (l : Λ)
    (h0 : 0 < M.mu false l) (h1 : 0 < M.mu true l) (k : Fin 4) :
    M.resp k l l = 0 := by
  set b₁ := (excluded k).1 with hb₁
  set b₂ := (excluded k).2 with hb₂
  have hsum : ∑ l₁, ∑ l₂, M.mu b₁ l₁ * M.mu b₂ l₂ * M.resp k l₁ l₂ = 0 := by
    rw [M.born k b₁ b₂, hb₁, hb₂, bornProb_excluded k]
  have hnonneg : ∀ l₁ ∈ (Finset.univ : Finset Λ), (0:ℝ) ≤
      ∑ l₂, M.mu b₁ l₁ * M.mu b₂ l₂ * M.resp k l₁ l₂ := by
    intro l₁ _
    exact Finset.sum_nonneg fun l₂ _ =>
      mul_nonneg (mul_nonneg (M.mu_nonneg _ _) (M.mu_nonneg _ _)) (M.resp_nonneg _ _ _)
  have h1' : ∑ l₂, M.mu b₁ l * M.mu b₂ l₂ * M.resp k l l₂ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum l (Finset.mem_univ l)
  have hnonneg2 : ∀ l₂ ∈ (Finset.univ : Finset Λ), (0:ℝ) ≤
      M.mu b₁ l * M.mu b₂ l₂ * M.resp k l l₂ := fun l₂ _ =>
    mul_nonneg (mul_nonneg (M.mu_nonneg _ _) (M.mu_nonneg _ _)) (M.resp_nonneg _ _ _)
  have hterm : M.mu b₁ l * M.mu b₂ l * M.resp k l l = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg2).1 h1' l (Finset.mem_univ l)
  have hpos₁ : 0 < M.mu b₁ l := by cases b₁ <;> assumption
  have hpos₂ : 0 < M.mu b₂ l := by cases b₂ <;> assumption
  have := mul_ne_zero (ne_of_gt hpos₁) (ne_of_gt hpos₂)
  exact by
    rcases mul_eq_zero.1 hterm with h | h
    · exact absurd h this
    · exact h

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of quantum
theory satisfying preparation independence, the quantum state is *ontic*: the
ontic-state distributions of two distinct pure states (here `|0⟩` and `|+⟩`)
have disjoint supports, so the quantum state is a function of the ontic state
and cannot be merely a state of knowledge about it. -/
theorem pbr_theorem (M : OntologicalModel Λ) (l : Λ) :
    M.mu false l = 0 ∨ M.mu true l = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  have h0' : 0 < M.mu false l := lt_of_le_of_ne (M.mu_nonneg _ _) (Ne.symm h0)
  have h1' : 0 < M.mu true l := lt_of_le_of_ne (M.mu_nonneg _ _) (Ne.symm h1)
  have hz : ∀ k : Fin 4, M.resp k l l = 0 :=
    fun k => resp_eq_zero_of_mem_overlap M l h0' h1' k
  have := M.resp_sum_one l l
  rw [Finset.sum_congr rfl (fun k _ => hz k)] at this
  simp at this

/-- Equivalent formulation: the supports of the two distributions are disjoint,
i.e. no ontic state is compatible with both preparations. -/
theorem pbr_no_overlap (M : OntologicalModel Λ) :
    ¬ ∃ l : Λ, 0 < M.mu false l ∧ 0 < M.mu true l := by
  rintro ⟨l, h0, h1⟩
  rcases pbr_theorem M l with h | h
  · exact absurd h (ne_of_gt h0)
  · exact absurd h (ne_of_gt h1)

end

end QI

