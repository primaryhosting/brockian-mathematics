/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace QI

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/
def tensor (a b : Qubit) : TwoQubit := fun i j => a i * b j

/-- The standard hermitian inner product on two-qubit vectors. -/
noncomputable def ip (v w : TwoQubit) : ℂ := ∑ i, ∑ j, (starRingEnd ℂ) (v i j) * w i j

/-- `1/√2`. -/
noncomputable def s2 : ℝ := (Real.sqrt 2)⁻¹

lemma s2_mul_s2 : (s2 : ℂ) * (s2 : ℂ) = 1 / 2 := by
  have h : s2 * s2 = 1 / 2 := by
    rw [s2, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_mul, h]
  norm_num

/-- The computational basis state `|0⟩`. -/
def ket0 : Qubit := ![1, 0]

/-- The state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def ketPlus : Qubit := ![(s2 : ℂ), (s2 : ℂ)]

/-- The two qubit states `|0⟩`, `|+⟩` used in the argument, indexed by `Fin 2`. -/
noncomputable def st : Fin 2 → Qubit := ![ket0, ketPlus]

/-- The four two-qubit product states `|00⟩, |0+⟩, |+0⟩, |++⟩` used in the
Pusey–Barrett–Rudolph argument. -/
noncomputable def prep : Fin 4 → Qubit × Qubit :=
  ![(ket0, ket0), (ket0, ketPlus), (ketPlus, ket0), (ketPlus, ketPlus)]

/-- The Pusey–Barrett–Rudolph measurement basis:
`(|01⟩+|10⟩)/√2`, `(|0-⟩+|1+⟩)/√2`, `(|+1⟩+|-0⟩)/√2`, `(|+-⟩+|-+⟩)/√2`. -/
noncomputable def pbrBasis : Fin 4 → TwoQubit :=
  ![ ![![0, (s2 : ℂ)], ![(s2 : ℂ), 0]],
     ![![1 / 2, -(1 / 2)], ![1 / 2, 1 / 2]],
     ![![1 / 2, 1 / 2], ![-(1 / 2), 1 / 2]],
     ![![(s2 : ℂ), 0], ![0, -(s2 : ℂ)]] ]

/-! ### The quantum input: the PBR basis is orthonormal and antidistinguishes -/

/-- The four PBR vectors form an orthonormal basis of the two-qubit space, so they
do describe a genuine projective measurement. -/
lemma pbrBasis_orthonormal (i j : Fin 4) :
    ip (pbrBasis i) (pbrBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ip, pbrBasis, Fin.sum_univ_two, Complex.ext_iff, s2_mul_s2] <;> ring_nf

/-- Antidistinguishability: the `k`-th outcome of the PBR measurement has Born
probability zero on the `k`-th of the four product states. -/
lemma pbrBasis_antidistinguishes (k : Fin 4) :
    ip (pbrBasis k) (tensor (prep k).1 (prep k).2) = 0 := by
  fin_cases k <;>
    simp [ip, pbrBasis, prep, tensor, ket0, ketPlus, Fin.sum_univ_two]

/-! ### The ontological-model argument -/

private lemma response_zero_at_overlap {Λ : Type*} [Fintype Λ]
    {μ : Qubit → Λ → ℝ} {ξ : Fin 4 → Λ → Λ → ℝ} {k : Fin 4} {a b : Qubit} {l : Λ}
    (hμ : ∀ a l, 0 ≤ μ a l) (hξ : ∀ k l₁ l₂, 0 ≤ ξ k l₁ l₂)
    (h : ∑ l₁, ∑ l₂, μ a l₁ * μ b l₂ * ξ k l₁ l₂ = 0)
    (hp : 0 < μ a l) (hq : 0 < μ b l) : ξ k l l = 0 := by
  have hinner : ∀ l₁ ∈ Finset.univ, 0 ≤ ∑ l₂, μ a l₁ * μ b l₂ * ξ k l₁ l₂ := by
    intro l₁ _
    exact Finset.sum_nonneg fun l₂ _ =>
      mul_nonneg (mul_nonneg (hμ _ _) (hμ _ _)) (hξ _ _ _)
  have h1 : ∑ l₂, μ a l * μ b l₂ * ξ k l l₂ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hinner).1 h l (Finset.mem_univ l)
  have h2 : ∀ l₂ ∈ Finset.univ, 0 ≤ μ a l * μ b l₂ * ξ k l l₂ := fun l₂ _ =>
    mul_nonneg (mul_nonneg (hμ _ _) (hμ _ _)) (hξ _ _ _)
  have h3 : μ a l * μ b l * ξ k l l = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg h2).1 h1 l (Finset.mem_univ l)
  rcases mul_eq_zero.1 h3 with h4 | h4
  · rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 (ne_of_gt hp)
    · exact absurd h5 (ne_of_gt hq)
  · exact h4

/--
**The Pusey–Barrett–Rudolph theorem** (the ψ-ontic conclusion for the pair
`|0⟩`, `|+⟩`).

Setting: an ontological model assigns to each pure quantum state `a` a
probability density `μ a` over a (finite) space `Λ` of ontic states, and to a
measurement on two systems a response function `ξ k l₁ l₂` giving the
probability of outcome `k` when the ontic states of the two systems are
`l₁, l₂` (so `∑ k, ξ k l₁ l₂ = 1`).

*Preparation independence* is the hypothesis `hborn`: when the two systems are
prepared independently in `a` and `b`, the joint ontic distribution is the
product `μ a ⊗ μ b`, and the model reproduces the quantum (Born) predictions
for the PBR measurement.

Conclusion: the distributions of the distinct, non-orthogonal states `|0⟩` and
`|+⟩` have disjoint supports; no ontic state is compatible with both. Hence the
quantum state cannot be merely epistemic: it is ontic.

Normalisation of the `μ a` is not needed for the argument, so it is not assumed.
-/
theorem pbr_theorem {Λ : Type*} [Fintype Λ]
    (μ : Qubit → Λ → ℝ) (ξ : Fin 4 → Λ → Λ → ℝ)
    (hμ : ∀ a l, 0 ≤ μ a l)
    (hξ : ∀ k l₁ l₂, 0 ≤ ξ k l₁ l₂)
    (hξsum : ∀ l₁ l₂, ∑ k, ξ k l₁ l₂ = 1)
    (hborn : ∀ j k : Fin 4,
      ∑ l₁, ∑ l₂, μ (prep j).1 l₁ * μ (prep j).2 l₂ * ξ k l₁ l₂
        = ‖ip (pbrBasis k) (tensor (prep j).1 (prep j).2)‖ ^ 2) :
    ∀ l : Λ, μ ket0 l = 0 ∨ μ ketPlus l = 0 := by
  intro l
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, hp⟩ := hcon
  have hp0 : 0 < μ ket0 l := lt_of_le_of_ne (hμ _ _) (Ne.symm h0)
  have hpp : 0 < μ ketPlus l := lt_of_le_of_ne (hμ _ _) (Ne.symm hp)
  have key : ∀ k : Fin 4, ξ k l l = 0 := by
    intro k
    have hb := hborn k k
    rw [pbrBasis_antidistinguishes k] at hb
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at hb
    fin_cases k <;>
      exact response_zero_at_overlap hμ hξ (by simpa [prep] using hb) (by assumption)
        (by assumption)
  have := hξsum l l
  rw [Finset.sum_congr rfl (fun k _ => key k)] at this
  simp at this

/-! ### Non-vacuity: the hypotheses of `pbr_theorem` are consistent -/

lemma s2_pos : 0 < s2 := by
  rw [s2]; exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

lemma ket0_ne_ketPlus : ket0 ≠ ketPlus := by
  intro h
  have h1 := congrFun h 1
  simp [ket0, ketPlus] at h1
  exact s2_pos.ne (by exact_mod_cast h1)

lemma s2_sq : s2 ^ 2 = 1 / 2 := by
  rw [s2, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

private lemma normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]

/-- Completeness of the PBR measurement on the four relevant product states: the
Born probabilities of its four outcomes sum to `1`. -/
lemma pbr_born_sum_one (l₁ l₂ : Fin 2) :
    ∑ k, ‖ip (pbrBasis k) (tensor (st l₁) (st l₂))‖ ^ 2 = 1 := by
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp [Fin.sum_univ_four, ip, pbrBasis, tensor, st, ket0, ketPlus, Fin.sum_univ_two,
      normsq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [s2_sq]

/-- The hypotheses of `pbr_theorem` are satisfiable, so the theorem is not vacuous:
the ψ-ontic model on two ontic states `Λ = Fin 2` (with `|0⟩` and `|+⟩` sitting on
the two different ontic states) satisfies all of them. -/
theorem exists_pbr_model :
    ∃ (μ : Qubit → Fin 2 → ℝ) (ξ : Fin 4 → Fin 2 → Fin 2 → ℝ),
      (∀ a l, 0 ≤ μ a l) ∧ (∀ k l₁ l₂, 0 ≤ ξ k l₁ l₂) ∧ (∀ l₁ l₂, ∑ k, ξ k l₁ l₂ = 1) ∧
      (∀ j k : Fin 4, ∑ l₁, ∑ l₂, μ (prep j).1 l₁ * μ (prep j).2 l₂ * ξ k l₁ l₂
        = ‖ip (pbrBasis k) (tensor (prep j).1 (prep j).2)‖ ^ 2) := by
  refine ⟨fun a l => if a = st l then 1 else 0,
    fun k l₁ l₂ => ‖ip (pbrBasis k) (tensor (st l₁) (st l₂))‖ ^ 2, ?_, ?_, pbr_born_sum_one, ?_⟩
  · intro a l; dsimp only; split <;> norm_num
  · intro k l₁ l₂; positivity
  · intro j k
    fin_cases j <;>
      simp [prep, st, Fin.sum_univ_two, ket0_ne_ketPlus, ket0_ne_ketPlus.symm]

end QI

#print axioms QI.pbr_theorem
#print axioms QI.exists_pbr_model
#print axioms QI.pbrBasis_orthonormal

