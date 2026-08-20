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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

/-- A primitive sixth root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6)

lemma om_primitive : IsPrimitiveRoot om 6 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 6 (by norm_num)

lemma om_pow_six : om ^ 6 = 1 := om_primitive.pow_eq_one

lemma om_pow_mod (a : ℕ) : om ^ (a % 6) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 6, pow_add, pow_mul, om_pow_six, one_pow, one_mul]

/-- The character `x ↦ ω ^ x` on `Fin 6` (i.e. on `ℤ/6ℤ`). -/
noncomputable def ee (x : Fin 6) : ℂ := om ^ (x : ℕ)

lemma ee_add (x y : Fin 6) : ee (x + y) = ee x * ee y := by
  simp only [ee, Fin.val_add, om_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_mul_neg (x : Fin 6) : ee x * ee (-x) = 1 := by
  rw [← ee_add]; simp [ee_zero]

lemma ee_pow (k x : Fin 6) : ee (k * x) = ee k ^ (x : ℕ) := by
  simp only [ee, Fin.val_mul, om_pow_mod, pow_mul]

lemma ee_injective : Function.Injective ee := fun i j h =>
  Fin.ext (om_primitive.pow_inj i.isLt j.isLt h)

lemma ee_eq_exp (k : Fin 6) :
    ee k = Complex.exp (((2 * Real.pi * (k : ℕ) / 6 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The adjacency matrix of the cycle graph `C₆`, with vertices indexed by `ℤ/6ℤ`
(realized as `Fin 6`): vertex `i` is adjacent to `i + 1` and to `i - 1`. -/
noncomputable def C6adj : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/6)` of benzene. -/
noncomputable def huckelEigenvalue (k : Fin 6) : ℂ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 6)

lemma ee_add_ee_neg (k : Fin 6) : ee k + ee (-k) = huckelEigenvalue k := by
  have h1 : ee (-k) = (ee k)⁻¹ := (inv_eq_of_mul_eq_one_right (ee_mul_neg k)).symm
  rw [h1, ee_eq_exp, huckelEigenvalue, Complex.ofReal_cos, Complex.cos, ← Complex.exp_neg]
  ring_nf

/-- Multiplication by the adjacency matrix of `C₆` is the discrete "shift-sum". -/
lemma C6adj_mulVec (v : Fin 6 → ℂ) (x : Fin 6) :
    C6adj.mulVec v x = v (x + 1) + v (x - 1) := by
  have hne : x + 1 ≠ x - 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    exact absurd (add_left_cancel h : (1 : Fin 6) = -1) (by decide)
  have key : ∀ j : Fin 6, (if j = x + 1 ∨ j = x - 1 then (1 : ℂ) else 0) * v j
      = (if j = x + 1 then v j else 0) + (if j = x - 1 then v j else 0) := by
    intro j
    by_cases h1 : j = x + 1 <;> by_cases h2 : j = x - 1 <;> simp_all
  simp only [C6adj, Matrix.mulVec, dotProduct, Matrix.of_apply, key, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The Fourier vector `x ↦ ω ^ (k x)` is an eigenvector of the adjacency matrix
of `C₆` with eigenvalue `2 cos (2πk/6)`. -/
theorem C6adj_mulVec_fourier (k : Fin 6) :
    C6adj.mulVec (fun x => ee (k * x)) = huckelEigenvalue k • (fun x => ee (k * x)) := by
  funext x
  rw [C6adj_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, ← ee_add_ee_neg]
  have h1 : k * (x + 1) = k * x + k := by rw [mul_add, mul_one]
  have h2 : k * (x - 1) = k * x + (-k) := by rw [mul_sub, mul_one, sub_eq_add_neg]
  rw [h1, h2, ee_add, ee_add]
  ring

/-- The Fourier (Vandermonde) matrix diagonalizing the adjacency matrix of `C₆`. -/
noncomputable def fourierMat : Matrix (Fin 6) (Fin 6) ℂ := Matrix.of fun x k => ee (k * x)

lemma fourierMat_eq : fourierMat = Matrix.transpose (Matrix.vandermonde ee) := by
  ext x k
  simp [fourierMat, Matrix.vandermonde, ee_pow]

lemma fourierMat_det_ne_zero : fourierMat.det ≠ 0 := by
  rw [fourierMat_eq, Matrix.det_transpose, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.1 hj)
  exact sub_ne_zero.2 fun h => hij (ee_injective h).symm

lemma C6adj_mul_fourierMat :
    C6adj * fourierMat = fourierMat * Matrix.diagonal huckelEigenvalue := by
  ext x k
  rw [Matrix.mul_diagonal]
  have hmul : (C6adj * fourierMat) x k = C6adj.mulVec (fun y => ee (k * y)) x := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, fourierMat]
  rw [hmul, congrFun (C6adj_mulVec_fourier k) x]
  simp [fourierMat, mul_comm]

/-- **Hückel theory for benzene (C₆).** The spectrum of the adjacency matrix of the
cycle graph `C₆` is exactly the set of numbers `2 cos (2πk/6)`, `k = 0, …, 5`. -/
theorem huckel_C6 :
    spectrum ℂ C6adj =
      Set.range (fun k : Fin 6 => (2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℂ)) := by
  obtain ⟨u, hu⟩ : IsUnit fourierMat :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fourierMat_det_ne_zero)
  have h : C6adj * (u : Matrix (Fin 6) (Fin 6) ℂ)
      = (u : Matrix (Fin 6) (Fin 6) ℂ) * Matrix.diagonal huckelEigenvalue := by
    rw [hu]; exact C6adj_mul_fourierMat
  have hconj : C6adj = (u : Matrix (Fin 6) (Fin 6) ℂ) * Matrix.diagonal huckelEigenvalue
      * ((u⁻¹ : (Matrix (Fin 6) (Fin 6) ℂ)ˣ) : Matrix (Fin 6) (Fin 6) ℂ) := by
    calc C6adj = C6adj * (u : Matrix (Fin 6) (Fin 6) ℂ) * (↑u⁻¹) := by
          rw [mul_assoc, u.mul_inv, mul_one]
      _ = _ := by rw [h]
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  rfl

end Chem

