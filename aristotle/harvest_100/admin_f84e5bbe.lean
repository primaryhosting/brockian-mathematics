/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

lemma om_primitive : IsPrimitiveRoot om 20 := by
  have := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [om] using this

lemma om_pow_20 : om ^ 20 = 1 := om_primitive.pow_eq_one

lemma om_ne_zero : om ≠ 0 := Complex.exp_ne_zero _

lemma om_pow_congr {a b : ℕ} (h : a % 20 = b % 20) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 20]
  conv_rhs => rw [← Nat.div_add_mod b 20]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_20, one_pow, one_pow, h]

/-- The eigenvector associated with the index `k`. -/
noncomputable def evec (k : Fin 20) : Fin 20 → ℂ := fun j => om ^ (j.val * k.val)

/-- The Hückel eigenvalue associated with the index `k`. -/
noncomputable def eval20 (k : Fin 20) : ℂ := (2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ)

lemma om_pow_add_om_pow (k : Fin 20) :
    om ^ (k : ℕ) + om ^ (19 * (k : ℕ)) = eval20 k := by
  set x : ℝ := 2 * Real.pi * (k : ℕ) / 20 with hx
  have h1 : om ^ (k : ℕ) = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul, hx]
    push_cast
    ring_nf
  have hmul : om ^ (19 * (k : ℕ)) * om ^ (k : ℕ) = 1 := by
    rw [← pow_add, show 19 * (k : ℕ) + (k : ℕ) = 20 * (k : ℕ) from by ring, pow_mul,
      om_pow_20, one_pow]
  have h2 : om ^ (19 * (k : ℕ)) = Complex.exp (-(x : ℂ) * Complex.I) := by
    rw [eq_inv_of_mul_eq_one_left hmul, h1, ← Complex.exp_neg]
    ring_nf
  rw [eval20, h1, h2, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  rw [Complex.two_cos, hx]
  push_cast
  ring_nf

lemma adj_mulVec (v : Fin 20 → ℂ) (i : Fin 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : ∀ i : Fin 20, (i - 1 : Fin 20) ≠ i + 1 := by decide
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (hne i)]

lemma evec_succ (k i : Fin 20) : evec k (i + 1) = evec k i * om ^ (k : ℕ) := by
  have h : ((i + 1 : Fin 20) : ℕ) = (i.val + 1) % 20 := Fin.val_add _ _
  simp only [evec, h]
  rw [om_pow_congr (a := ((i.val + 1) % 20) * k.val) (b := (i.val + 1) * k.val)
    (by simp [Nat.mul_mod]), add_mul, one_mul, pow_add]

lemma evec_pred (k i : Fin 20) : evec k (i - 1) = evec k i * om ^ (19 * (k : ℕ)) := by
  have h19 : (i - 1 : Fin 20) = i + 19 := by revert i; decide
  have h : ((i + 19 : Fin 20) : ℕ) = (i.val + 19) % 20 := Fin.val_add _ _
  simp only [evec, h19, h]
  rw [om_pow_congr (a := ((i.val + 19) % 20) * k.val) (b := (i.val + 19) * k.val)
    (by simp [Nat.mul_mod]), add_mul, pow_add]

lemma evec_eigen (k : Fin 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec (evec k) = eval20 k • evec k := by
  funext i
  rw [adj_mulVec, evec_succ, evec_pred, Pi.smul_apply, smul_eq_mul, ← om_pow_add_om_pow k]
  ring

lemma evec_ne_zero (k : Fin 20) : evec k ≠ 0 := by
  intro h
  have : evec k 0 = 0 := by rw [h]; rfl
  simp [evec] at this

/-- The (Vandermonde / discrete Fourier) matrix whose columns are the eigenvectors. -/
noncomputable def U : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.vandermonde (fun j : Fin 20 => om ^ (j : ℕ))

lemma U_apply (j k : Fin 20) : U j k = evec k j := by
  simp [U, Matrix.vandermonde, evec, ← pow_mul]

lemma U_det_ne_zero : U.det ≠ 0 := by
  rw [U, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro h
  exact absurd (Fin.ext (om_primitive.pow_inj j.isLt i.isLt h)) (Finset.mem_Ioi.mp hj).ne'

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def D : Matrix (Fin 20) (Fin 20) ℂ := Matrix.diagonal eval20

lemma adj_mul_U : ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) * U = U * D := by
  ext i k
  have hcol : (fun j => U j k) = evec k := funext fun j => U_apply j k
  have h1 : (((SimpleGraph.cycleGraph 20).adjMatrix ℂ) * U) i k
      = ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec (evec k) i := by
    rw [Matrix.mul_apply, ← hcol]
    rfl
  rw [h1, evec_eigen, Pi.smul_apply, smul_eq_mul, D, Matrix.mul_diagonal, U_apply,
    mul_comm]

/-- **Hückel theory for C₂₀.**  A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₂₀` if and only if it is of the form `2 cos (2πk/20)` for some
`k ∈ {0, …, 19}`. -/
theorem huckel_C20 (μ : ℂ) :
    (∃ v : Fin 20 → ℂ, v ≠ 0 ∧
        ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : Fin 20, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hU : IsUnit U.det := isUnit_iff_ne_zero.mpr U_det_ne_zero
    set y : Fin 20 → ℂ := U⁻¹.mulVec x with hy
    have hUy : U.mulVec y = x := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U hU, Matrix.one_mulVec]
    have hy0 : y ≠ 0 := by
      intro h
      apply hx0
      rw [← hUy, h, Matrix.mulVec_zero]
    have key : U.mulVec (D.mulVec y) = U.mulVec (μ • y) := by
      rw [Matrix.mulVec_mulVec, ← adj_mul_U, ← Matrix.mulVec_mulVec, hUy, hx,
        Matrix.mulVec_smul, hUy]
    have hDy : D.mulVec y = μ • y := by
      have h := congrArg (fun z => U⁻¹.mulVec z) key
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul U hU,
        Matrix.one_mul, Matrix.one_mulVec] at h
      exact h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hy0
    refine ⟨k, ?_⟩
    have := congrFun hDy k
    rw [D, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    have hμ : μ = eval20 k := (mul_right_cancel₀ hk this).symm
    simpa [eval20] using hμ
  · rintro ⟨k, rfl⟩
    exact ⟨evec k, evec_ne_zero k, by simpa [eval20] using evec_eigen k⟩

end Chem

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

