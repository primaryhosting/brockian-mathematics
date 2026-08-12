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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above

Category: Zeta-23 §3 Linear Algebra (re-derivation)

Target: `Zeta23Redux.LinAlg.weyl_posIndexAbove`

For a Hermitian matrix `A` over `ℂ` of size `Fin d` we define

* `posIndex hA`, the number of strictly positive eigenvalues of `A`;
* `posIndexAbove hA θ`, the number of eigenvalues of `A` strictly above `θ`.

The main result `weyl_posIndexAbove` is Weyl's monotonicity statement: if all eigenvalues of a
Hermitian perturbation `E` are bounded in absolute value by `θ`, then
`posIndexAbove (A + E) θ ≤ posIndex A`.

The proof is the Courant–Fischer/interlacing argument in its subspace form: the span of the
eigenvectors of `A + E` with eigenvalue `> θ` intersects trivially the span of the eigenvectors of
`A` with eigenvalue `≤ 0`, because on the first subspace the quadratic form of `A + E` is `> θ‖x‖²`
while on the second one it is `≤ 0 + θ‖x‖²`.  Comparing dimensions gives the claim.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The number of eigenvalues of a Hermitian matrix that are strictly above `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => θ < hA.eigenvalues i).card

lemma posIndex_eq_posIndexAbove_zero {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    posIndex hA = posIndexAbove hA 0 := rfl

section Quadratic

variable {M : Matrix (Fin d) (Fin d) ℂ}

/-- The eigenvector basis diagonalizes the associated linear map. -/
lemma toEuclideanLin_eigenvectorBasis (hM : M.IsHermitian) (i : Fin d) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i)
      = (hM.eigenvalues i : ℂ) • (hM.eigenvectorBasis i) := by
  have h := hM.mulVec_eigenvectorBasis i
  rw [show Matrix.toEuclideanLin M = Matrix.toLpLin 2 2 M from rfl, Matrix.toLpLin_apply, h,
    RCLike.real_smul_eq_coe_smul (K := ℂ), WithLp.toLp_smul, WithLp.toLp_ofLp]
  rfl

/-- The coefficient of `M x` along the `i`-th eigenvector. -/
lemma inner_eigenvectorBasis_apply (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    inner ℂ (hM.eigenvectorBasis i) (Matrix.toEuclideanLin M x)
      = (hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x := by
  have hs := Matrix.isHermitian_iff_isSymmetric.1 hM
  rw [← hs, toEuclideanLin_eigenvectorBasis hM i, inner_smul_left]
  simp

/-- Parseval identity for the eigenvector basis. -/
lemma sum_norm_inner_sq (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) :
    ∑ i, ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have key := hM.eigenvectorBasis.sum_inner_mul_inner x x
  have h2 : ∀ i : Fin d, (inner ℂ x (hM.eigenvectorBasis i) : ℂ) * inner ℂ (hM.eigenvectorBasis i) x
      = ((‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm x (hM.eigenvectorBasis i), RCLike.conj_mul]
    push_cast; rfl
  simp_rw [h2, ← Complex.ofReal_sum] at key
  rw [inner_self_eq_norm_sq_to_K] at key
  have h3 : ((∑ i, ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [key]; push_cast; rfl
  exact Complex.ofReal_inj.mp h3

/-- The quadratic form of a Hermitian matrix expressed through its eigenvalues. -/
lemma quadForm_eq_sum (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) :
    (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ).re
      = ∑ i, hM.eigenvalues i * ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 := by
  have key := hM.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin M x)
  have h2 : ∀ i : Fin d,
      (inner ℂ x (hM.eigenvectorBasis i) : ℂ) * inner ℂ (hM.eigenvectorBasis i)
        (Matrix.toEuclideanLin M x)
      = ((hM.eigenvalues i * ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [inner_eigenvectorBasis_apply hM x i, ← inner_conj_symm x (hM.eigenvectorBasis i)]
    rw [show (starRingEnd ℂ) (inner ℂ (hM.eigenvectorBasis i) x) *
        ((hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x)
        = (hM.eigenvalues i : ℂ) * ((starRingEnd ℂ) (inner ℂ (hM.eigenvectorBasis i) x)
          * inner ℂ (hM.eigenvectorBasis i) x) by ring, RCLike.conj_mul]
    push_cast; rfl
  simp_rw [h2, ← Complex.ofReal_sum] at key
  rw [← key, Complex.ofReal_re]

/-- If all eigenvalues occurring in the expansion of `x` are `≤ c`, the quadratic form is
bounded by `c‖x‖²`. -/
lemma quadForm_le (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (c : ℝ)
    (h : ∀ i, inner ℂ (hM.eigenvectorBasis i) x ≠ 0 → hM.eigenvalues i ≤ c) :
    (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ).re ≤ c * ‖x‖ ^ 2 := by
  rw [quadForm_eq_sum hM x, ← sum_norm_inner_sq hM x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases eq_or_ne (inner ℂ (hM.eigenvectorBasis i) x) 0 with h0 | h0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (h i h0) (by positivity)

/-- If all eigenvalues occurring in the expansion of a nonzero `x` are `> c`, the quadratic form
is strictly bigger than `c‖x‖²`. -/
lemma quadForm_gt (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (c : ℝ) (hx : x ≠ 0)
    (h : ∀ i, inner ℂ (hM.eigenvectorBasis i) x ≠ 0 → c < hM.eigenvalues i) :
    c * ‖x‖ ^ 2 < (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ).re := by
  rw [quadForm_eq_sum hM x, ← sum_norm_inner_sq hM x, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ?_
  · rcases eq_or_ne (inner ℂ (hM.eigenvectorBasis i) x) 0 with h0 | h0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (h i h0).le (by positivity)
  · have hne : ∃ i, inner ℂ (hM.eigenvectorBasis i) x ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      have hsum := sum_norm_inner_sq hM x
      simp [hc] at hsum
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_right (h i hi) (by positivity)⟩

end Quadratic

section Span

/-- A vector orthogonal to a spanning family is orthogonal to everything in the span. -/
lemma inner_eq_zero_of_mem_span {ι : Type*} (f : ι → EuclideanSpace ℂ (Fin d))
    (v x : EuclideanSpace ℂ (Fin d)) (hx : x ∈ Submodule.span ℂ (Set.range f))
    (hv : ∀ j, inner ℂ v (f j) = 0) : inner ℂ v x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hv j
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]

/-- The span of a subfamily of the eigenvector basis has dimension the size of the subfamily. -/
lemma finrank_span_eigenvectors {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (p : Fin d → Prop) [DecidablePred p] :
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun i : {i // p i} => (hM.eigenvectorBasis i.1 :
          EuclideanSpace ℂ (Fin d))))
      = (Finset.univ.filter p).card := by
  have hli : LinearIndependent ℂ (fun i : {i // p i} => (hM.eigenvectorBasis i.1 :
      EuclideanSpace ℂ (Fin d))) :=
    (hM.eigenvectorBasis.orthonormal.linearIndependent).comp _ Subtype.val_injective
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

end Span

/-- **Weyl monotonicity**: if all eigenvalues of the Hermitian perturbation `E` are bounded
in absolute value by `θ`, then the number of eigenvalues of `A + E` strictly above `θ`
is at most the number of strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {d : ℕ} {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  set hB := hA.add hE with hBdef
  set W1 := Submodule.span ℂ (Set.range fun i : {i // θ < hB.eigenvalues i} =>
    (hB.eigenvectorBasis i.1 : EuclideanSpace ℂ (Fin d))) with hW1
  set W2 := Submodule.span ℂ (Set.range fun i : {i // ¬ (0 < hA.eigenvalues i)} =>
    (hA.eigenvectorBasis i.1 : EuclideanSpace ℂ (Fin d))) with hW2
  -- the two subspaces intersect trivially
  have hinf : W1 ⊓ W2 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Submodule.mem_bot]
    by_contra hxne
    have hz1 : ∀ i, inner ℂ (hB.eigenvectorBasis i) x ≠ 0 → θ < hB.eigenvalues i := by
      intro i hi
      by_contra hle
      refine hi (inner_eq_zero_of_mem_span _ _ _ hx1 fun j => ?_)
      have hij : i ≠ j.1 := by rintro rfl; exact hle j.2
      exact hB.eigenvectorBasis.orthonormal.2 hij
    have hz2 : ∀ i, inner ℂ (hA.eigenvectorBasis i) x ≠ 0 → hA.eigenvalues i ≤ 0 := by
      intro i hi
      by_contra hpos
      push_neg at hpos
      refine hi (inner_eq_zero_of_mem_span _ _ _ hx2 fun j => ?_)
      have hij : i ≠ j.1 := by rintro rfl; exact j.2 hpos
      exact hA.eigenvectorBasis.orthonormal.2 hij
    have hgt : θ * ‖x‖ ^ 2 < (inner ℂ x (Matrix.toEuclideanLin (A + E) x) : ℂ).re :=
      quadForm_gt hB x θ hxne hz1
    have hAle : (inner ℂ x (Matrix.toEuclideanLin A x) : ℂ).re ≤ 0 * ‖x‖ ^ 2 :=
      quadForm_le hA x 0 hz2
    have hEle : (inner ℂ x (Matrix.toEuclideanLin E x) : ℂ).re ≤ θ * ‖x‖ ^ 2 :=
      quadForm_le hE x θ fun i _ => (abs_le.mp (hEθ i)).2
    have hadd : (inner ℂ x (Matrix.toEuclideanLin (A + E) x) : ℂ).re
        = (inner ℂ x (Matrix.toEuclideanLin A x) : ℂ).re
          + (inner ℂ x (Matrix.toEuclideanLin E x) : ℂ).re := by
      rw [map_add, LinearMap.add_apply, inner_add_right, Complex.add_re]
    linarith
  -- dimensions
  have h1 : Module.finrank ℂ W1 = posIndexAbove hB θ := finrank_span_eigenvectors hB _
  have h2 : Module.finrank ℂ W2
      = (Finset.univ.filter fun i => ¬ (0 < hA.eigenvalues i)).card :=
    finrank_span_eigenvectors hA _
  have hsup : Module.finrank ℂ (W1 ⊔ W2 : Submodule ℂ (EuclideanSpace ℂ (Fin d))) ≤ d := by
    have := Submodule.finrank_le (W1 ⊔ W2)
    rwa [finrank_euclideanSpace_fin] at this
  have hkey : Module.finrank ℂ W1 + Module.finrank ℂ W2 ≤ d := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W1 W2
    rw [hinf] at h
    simp only [finrank_bot, add_zero] at h
    omega
  have hcard : posIndex hA + (Finset.univ.filter fun i => ¬ (0 < hA.eigenvalues i)).card = d := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d)))
      (fun i => 0 < hA.eigenvalues i)
    simpa [posIndex] using this
  omega

/-- Sanity check that the hypotheses of `weyl_posIndexAbove` are satisfiable: taking the zero
perturbation and `θ = 0` recovers the trivial inequality. -/
example {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    posIndexAbove (hA.add Matrix.isHermitian_zero) 0 ≤ posIndex hA :=
  weyl_posIndexAbove hA Matrix.isHermitian_zero 0 (fun i => by
    have h : (Matrix.isHermitian_zero (n := Fin d) (α := ℂ)).eigenvalues = 0 :=
      (Matrix.IsHermitian.eigenvalues_eq_zero_iff _).2 rfl
    simp [h])

end Zeta23Redux.LinAlg

