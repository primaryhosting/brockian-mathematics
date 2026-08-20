import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
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

namespace Math2

open Matrix

variable {n : ℕ}

/-- The standard symplectic form on `ℝ ^ (2 * n)`, with `ℝ ^ (2 * n)` modelled as functions
`(Fin n ⊕ Fin n) → ℝ`: the coordinates indexed by `Sum.inl i` are the positions `qᵢ` and the
coordinates indexed by `Sum.inr i` are the momenta `pᵢ`. -/
def omegaForm (x y : (Fin n ⊕ Fin n) → ℝ) : ℝ :=
  ∑ i : Fin n, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i))

/-- The closed Euclidean ball of radius `r` centred at the origin in `ℝ ^ (2 * n)`. -/
def ball (r : ℝ) : Set ((Fin n ⊕ Fin n) → ℝ) := {x | ∑ k, x k ^ 2 ≤ r ^ 2}

/-- The symplectic cylinder of radius `R` over the `i₀`-th coordinate plane: the set of points
whose `(qᵢ₀, pᵢ₀)`-coordinates lie in the closed disc of radius `R`. -/
def cylinder (i₀ : Fin n) (R : ℝ) : Set ((Fin n ⊕ Fin n) → ℝ) :=
  {y | y (Sum.inl i₀) ^ 2 + y (Sum.inr i₀) ^ 2 ≤ R ^ 2}

/-- The symplectic form written through the matrix `J`. -/
lemma omegaForm_eq_dotProduct (x y : (Fin n ⊕ Fin n) → ℝ) :
    omegaForm x y = -(x ⬝ᵥ (Matrix.J (Fin n) ℝ *ᵥ y)) := by
  simp [omegaForm, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.one_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- Matrices in the symplectic group act on `ℝ ^ (2 * n)` by symplectic linear maps: they preserve
the standard symplectic form `omegaForm`. -/
lemma omegaForm_mulVec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (x y : (Fin n ⊕ Fin n) → ℝ) :
    omegaForm (A *ᵥ x) (A *ᵥ y) = omegaForm x y := by
  have hA' : Aᵀ * Matrix.J (Fin n) ℝ * A = Matrix.J (Fin n) ℝ := SymplecticGroup.mem_iff'.1 hA
  rw [omegaForm_eq_dotProduct, omegaForm_eq_dotProduct]
  congr 1
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA']

/-- The key algebraic consequence of the symplectic condition `A * J * Aᵀ = J`: the two rows of `A`
indexed by `Sum.inl i₀` and `Sum.inr i₀` pair to `1` under the symplectic form. -/
lemma rows_omegaForm {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (i₀ : Fin n) :
    ∑ j : Fin n, (A (Sum.inl i₀) (Sum.inr j) * A (Sum.inr i₀) (Sum.inl j)
      - A (Sum.inl i₀) (Sum.inl j) * A (Sum.inr i₀) (Sum.inr j)) = -1 := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.1 hA) (Sum.inl i₀)) (Sum.inr i₀)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_sub_distrib] at h ⊢
  linarith [h]

/-- If the image of the ball of radius `r` under the affine map `x ↦ A *ᵥ x + b` lies in the
cylinder of radius `R`, then each of the two relevant rows `A a` of `A` satisfies
`r ^ 2 * ‖A a‖ ^ 2 ≤ R ^ 2`. -/
lemma sq_row_bound {i₀ : Fin n} {r R : ℝ}
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {b : (Fin n ⊕ Fin n) → ℝ}
    (h : (fun x => A *ᵥ x + b) '' ball r ⊆ cylinder i₀ R)
    {a : Fin n ⊕ Fin n} (ha : a = Sum.inl i₀ ∨ a = Sum.inr i₀) :
    r ^ 2 * (∑ k, A a k ^ 2) ≤ R ^ 2 := by
  set S : ℝ := ∑ k, A a k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases eq_or_lt_of_le hS0 with hzero | hpos
  · rw [← hzero, mul_zero]
    positivity
  · have hsq : 0 < Real.sqrt S := Real.sqrt_pos.2 hpos
    set c : ℝ := r / Real.sqrt S with hc
    have hcS : c ^ 2 * S = r ^ 2 := by
      rw [hc, div_pow, Real.sq_sqrt hS0]
      field_simp
    -- the two antipodal points of the ball in the direction of the row `A a`
    have main : ∀ t : ℝ, t ^ 2 = 1 → (t * c * S + b a) ^ 2 ≤ R ^ 2 := by
      intro t ht
      set x : (Fin n ⊕ Fin n) → ℝ := fun k => (t * c) * A a k with hx
      have hmem : x ∈ ball r := by
        show ∑ k, x k ^ 2 ≤ r ^ 2
        have hxs : ∑ k, x k ^ 2 = c ^ 2 * S := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hx]
          nlinarith [ht]
        rw [hxs, hcS]
      have hcyl := h ⟨x, hmem, rfl⟩
      have hval : (A *ᵥ x + b) a = t * c * S + b a := by
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct, hx, hS]
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
      have hcyl' : (A *ᵥ x + b) (Sum.inl i₀) ^ 2 + (A *ᵥ x + b) (Sum.inr i₀) ^ 2 ≤ R ^ 2 := hcyl
      have hkey : ((A *ᵥ x + b) a) ^ 2 ≤ R ^ 2 := by
        rcases ha with rfl | rfl
        · nlinarith [sq_nonneg ((A *ᵥ x + b) (Sum.inr i₀))]
        · nlinarith [sq_nonneg ((A *ᵥ x + b) (Sum.inl i₀))]
      rwa [hval] at hkey
    have h₁ := main 1 (by norm_num)
    have h₂ := main (-1) (by norm_num)
    have hkey : (c * S) ^ 2 ≤ R ^ 2 := by nlinarith [h₁, h₂]
    calc r ^ 2 * S = (c ^ 2 * S) * S := by rw [hcS]
      _ = (c * S) ^ 2 := by ring
      _ ≤ R ^ 2 := hkey

/-- **Gromov's nonsqueezing theorem for affine symplectic maps.**

If an affine symplectomorphism `x ↦ A *ᵥ x + b` of `ℝ ^ (2 * n)` (with `A` in the symplectic group,
so that the map preserves the standard symplectic form, cf. `Math2.omegaForm_mulVec`) maps the
closed ball of radius `r` into the symplectic cylinder of radius `R` over the `i₀`-th coordinate
symplectic plane, then `r ≤ R`. -/
theorem gromov_nonsqueezing_affine {n : ℕ} {i₀ : Fin n} {r R : ℝ} (hR : 0 ≤ R)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {b : (Fin n ⊕ Fin n) → ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (h : (fun x => A *ᵥ x + b) '' ball r ⊆ cylinder i₀ R) :
    r ≤ R := by
  set u : (Fin n ⊕ Fin n) → ℝ := fun k => A (Sum.inl i₀) k with hu
  set v : (Fin n ⊕ Fin n) → ℝ := fun k => A (Sum.inr i₀) k with hv
  set w : (Fin n ⊕ Fin n) → ℝ := Sum.elim (fun j => u (Sum.inr j)) (fun j => -u (Sum.inl j))
    with hw
  set S : ℝ := ∑ k, u k ^ 2 with hSdef
  set T : ℝ := ∑ k, v k ^ 2 with hTdef
  have hwv : ∑ k, w k * v k = -1 := by
    rw [Fintype.sum_sum_type]
    have := rows_omegaForm hA i₀
    simp only [hw, hu, hv, Sum.elim_inl, Sum.elim_inr]
    rw [← this, Finset.sum_sub_distrib]
    simp [neg_mul]
    ring
  have hww : ∑ k, w k ^ 2 = S := by
    rw [hSdef, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [hw]
    ring
  have hCS : (∑ k, w k * v k) ^ 2 ≤ (∑ k, w k ^ 2) * ∑ k, v k ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hST : 1 ≤ S * T := by
    rw [hwv, hww, ← hTdef] at hCS
    linarith [hCS]
  have hSb : r ^ 2 * S ≤ R ^ 2 := sq_row_bound h (Or.inl rfl)
  have hTb : r ^ 2 * T ≤ R ^ 2 := sq_row_bound h (Or.inr rfl)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h4 : r ^ 4 ≤ R ^ 4 := by
    have hmul : (r ^ 2 * S) * (r ^ 2 * T) ≤ R ^ 2 * R ^ 2 := by
      apply mul_le_mul hSb hTb (by positivity) (by positivity)
    nlinarith [sq_nonneg r, sq_nonneg R]
  exact le_of_pow_le_pow_left₀ (by norm_num) hR h4

/-- **Gromov's nonsqueezing theorem, linear case.**

If a linear symplectomorphism of `ℝ ^ (2 * n)` (given by a matrix `A` in the symplectic group, so
that `x ↦ A *ᵥ x` preserves the standard symplectic form, cf. `Math2.omegaForm_mulVec`) maps the
closed ball of radius `r` into the symplectic cylinder of radius `R` over the `i₀`-th coordinate
symplectic plane, then `r ≤ R`: a symplectic linear map cannot squeeze a ball into a thinner
cylinder. (No sign assumption on `r` is needed: for `r < 0` the conclusion is immediate from
`0 ≤ R`.)

(This is the linear version of Gromov's nonsqueezing theorem; the general version, for arbitrary
symplectic embeddings, requires the theory of pseudoholomorphic curves. The affine version is
`Math2.gromov_nonsqueezing_affine`.) -/
theorem gromov_nonsqueezing {n : ℕ} {i₀ : Fin n} {r R : ℝ} (hR : 0 ≤ R)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (h : (fun x => A *ᵥ x) '' ball r ⊆ cylinder i₀ R) :
    r ≤ R :=
  gromov_nonsqueezing_affine (b := 0) hR hA (by simpa using h)

/-- Sanity check (non-vacuity): the hypotheses of `Math2.gromov_nonsqueezing` are satisfiable, e.g.
by the identity map with `r = R = 1`. -/
example : ((fun x => (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) *ᵥ x) '' ball 1
    ⊆ cylinder (0 : Fin 1) 1) := by
  rintro y ⟨x, hx, rfl⟩
  have hx' : ∑ k, x k ^ 2 ≤ 1 ^ 2 := hx
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton] at hx'
  simp only [Matrix.one_mulVec]
  show x (Sum.inl 0) ^ 2 + x (Sum.inr 0) ^ 2 ≤ 1 ^ 2
  linarith

end Math2

