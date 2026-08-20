/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

/-- The adjacency matrix of the cycle graph `C₁₉` (the Hückel matrix of the
19-membered annulene, in units where `α = 0` and `β = 1`). -/
noncomputable def C19adj : Matrix (Fin 19) (Fin 19) ℂ := (cycleGraph 19).adjMatrix ℂ

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/19)`. -/
noncomputable def huckelEigenvalue (k : ℕ) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)

/-- The (unnormalised) discrete Fourier matrix; its `k`-th column is the eigenvector
of `C19adj` for the eigenvalue `2 cos (2πk/19)`. -/
noncomputable def dftP : Matrix (Fin 19) (Fin 19) ℂ := fun j k => zeta ^ (j.val * k.val)

/-- The inverse discrete Fourier matrix. -/
noncomputable def dftQ : Matrix (Fin 19) (Fin 19) ℂ :=
  fun k j => (19 : ℂ)⁻¹ * (zeta ^ (k.val * j.val))⁻¹

lemma zeta_primitive : IsPrimitiveRoot zeta 19 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 19 (by norm_num)

lemma zeta_pow_19 : zeta ^ 19 = 1 := zeta_primitive.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := by
  intro h
  simpa [h] using zeta_pow_19

lemma zeta_pow_ne_zero (m : ℕ) : zeta ^ m ≠ 0 := pow_ne_zero _ zeta_ne_zero

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 19) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, zeta_pow_19, one_pow, one_mul]

lemma zeta_pow_congr {m n : ℕ} (h : m % 19 = n % 19) : zeta ^ m = zeta ^ n := by
  rw [← zeta_pow_mod m, ← zeta_pow_mod n, h]

/-- Orthogonality of the discrete Fourier characters: `∑ⱼ ζ^(aj) ζ^(-jb) = 19·[a = b]`. -/
lemma dft_sum (a b : Fin 19) :
    ∑ j : Fin 19, zeta ^ (a.val * j.val) * (zeta ^ (j.val * b.val))⁻¹ =
      if a = b then (19 : ℂ) else 0 := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = zeta ^ a.val * (zeta ^ b.val)⁻¹ := ⟨_, rfl⟩
  have hterm : ∀ j : Fin 19, zeta ^ (a.val * j.val) * (zeta ^ (j.val * b.val))⁻¹ = w ^ j.val := by
    intro j
    have h1 : w ^ j.val = (zeta ^ a.val) ^ j.val * ((zeta ^ b.val) ^ j.val)⁻¹ := by
      rw [hw, mul_pow, inv_pow]
    rw [h1, ← pow_mul, ← pow_mul, mul_comm b.val j.val]
  have hw19 : w ^ 19 = 1 := by
    have h1 : w ^ 19 = (zeta ^ a.val) ^ 19 * ((zeta ^ b.val) ^ 19)⁻¹ := by
      rw [hw, mul_pow, inv_pow]
    rw [h1, ← pow_mul, ← pow_mul, mul_comm a.val 19, mul_comm b.val 19, pow_mul, pow_mul,
      zeta_pow_19, one_pow, one_pow, inv_one, mul_one]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Fin.sum_univ_eq_sum_range (fun i => w ^ i) 19]
  by_cases hab : a = b
  · subst hab
    have hw1 : w = 1 := by rw [hw, mul_inv_cancel₀ (zeta_pow_ne_zero a.val)]
    simp [hw1]
  · have hwne : w ≠ 1 := by
      intro h
      apply hab
      rw [hw, mul_inv_eq_one₀ (zeta_pow_ne_zero b.val)] at h
      exact Fin.ext (zeta_primitive.pow_inj a.isLt b.isLt h)
    rw [geom_sum_eq hwne, hw19]
    simp [hab]

lemma dftP_mul_dftQ : dftP * dftQ = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 19, dftP a j * dftQ j b
      = (19 : ℂ)⁻¹ * (zeta ^ (a.val * j.val) * (zeta ^ (j.val * b.val))⁻¹) := by
    intro j; simp only [dftP, dftQ]; ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, dft_sum]
  by_cases hab : a = b <;> simp [hab, Matrix.one_apply]

lemma dftQ_mul_dftP : dftQ * dftP = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 19, dftQ a j * dftP j b
      = (19 : ℂ)⁻¹ * (zeta ^ (b.val * j.val) * (zeta ^ (j.val * a.val))⁻¹) := by
    intro j
    simp only [dftP, dftQ]
    rw [mul_comm a.val j.val, mul_comm j.val b.val]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, dft_sum]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Ne.symm hab, hab]

lemma zeta_pow_add_inv (k : ℕ) : zeta ^ k + (zeta ^ k)⁻¹ = huckelEigenvalue k := by
  have h1 : zeta ^ k = Complex.exp (((2 * Real.pi * k / 19 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [huckelEigenvalue, h1, ← Complex.exp_neg, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- The adjacency relation of `C₁₉`. -/
lemma cycle19_adj_iff (u v : Fin 19) :
    (cycleGraph 19).Adj u v ↔ (v = u + 1 ∨ v = u - 1) := by
  revert u v
  decide

/-- `C19adj` acts on the `k`-th Fourier column by multiplication by `2 cos (2πk/19)`. -/
lemma C19adj_mul_dftP :
    C19adj * dftP = dftP * diagonal (fun k : Fin 19 => huckelEigenvalue k.val) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hsub : j - 1 = j + 18 := by revert j; decide
  have hne : (j + 1) ≠ (j - 1) := by revert j; decide
  have hterm : ∀ i : Fin 19, C19adj j i * dftP i k
      = if i ∈ ({j + 1, j - 1} : Finset (Fin 19)) then dftP i k else 0 := by
    intro i
    simp only [C19adj, SimpleGraph.adjMatrix_apply, Finset.mem_insert, Finset.mem_singleton]
    by_cases h : (cycleGraph 19).Adj j i
    · rw [if_pos h, one_mul, if_pos ((cycle19_adj_iff j i).1 h)]
    · rw [if_neg h, zero_mul, if_neg (fun hc => h ((cycle19_adj_iff j i).2 hc))]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]
  -- now compute the two Fourier entries
  have e1 : dftP (j + 1) k = zeta ^ (j.val * k.val) * zeta ^ k.val := by
    have hval : (j + 1).val = (j.val + 1) % 19 := rfl
    calc dftP (j + 1) k = zeta ^ (((j.val + 1) % 19) * k.val) := by rw [dftP, hval]
      _ = zeta ^ ((j.val + 1) * k.val) := by
          exact zeta_pow_congr (Nat.ModEq.mul_right k.val (Nat.mod_mod_of_dvd _ dvd_rfl))
      _ = zeta ^ (j.val * k.val) * zeta ^ k.val := by rw [add_mul, one_mul, pow_add]
  have e2 : dftP (j - 1) k = zeta ^ (j.val * k.val) * (zeta ^ k.val)⁻¹ := by
    have hj : j - 1 = j + 18 := hsub
    have hval : (j + 18).val = (j.val + 18) % 19 := rfl
    have hinv : zeta ^ (18 * k.val) = (zeta ^ k.val)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_add]
      have h19 : 18 * k.val + k.val = 19 * k.val := by ring
      rw [h19, pow_mul, zeta_pow_19, one_pow]
    calc dftP (j - 1) k = zeta ^ (((j.val + 18) % 19) * k.val) := by rw [hj, dftP, hval]
      _ = zeta ^ ((j.val + 18) * k.val) := by
          exact zeta_pow_congr (Nat.ModEq.mul_right k.val (Nat.mod_mod_of_dvd _ dvd_rfl))
      _ = zeta ^ (j.val * k.val) * (zeta ^ k.val)⁻¹ := by
          rw [add_mul, pow_add, hinv]
  rw [e1, e2, ← mul_add, zeta_pow_add_inv k.val, dftP]

/-- **Hückel theory for C₁₉.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₉` factors as `∏_{k=0}^{18} (X - 2 cos (2πk/19))`; that is, the adjacency
eigenvalues of `C₁₉` are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
theorem huckel_C19 :
    C19adj.charpoly =
      ∏ k ∈ Finset.range 19, (X - C ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)) := by
  let u : (Matrix (Fin 19) (Fin 19) ℂ)ˣ :=
    ⟨dftP, dftQ, dftP_mul_dftQ, dftQ_mul_dftP⟩
  have hu : (↑u : Matrix (Fin 19) (Fin 19) ℂ) = dftP := rfl
  have huinv : (↑u⁻¹ : Matrix (Fin 19) (Fin 19) ℂ) = dftQ := rfl
  have hA : C19adj = (↑u : Matrix (Fin 19) (Fin 19) ℂ) *
      diagonal (fun k : Fin 19 => huckelEigenvalue k.val) *
      (↑u⁻¹ : Matrix (Fin 19) (Fin 19) ℂ) := by
    rw [hu, huinv, ← C19adj_mul_dftP, Matrix.mul_assoc, dftP_mul_dftQ, Matrix.mul_one]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal,
    Fin.prod_univ_eq_prod_range (fun i => X - C (huckelEigenvalue i)) 19]
  rfl

/-- The explicit Hückel eigenvectors of `C₁₉`: the Fourier mode `j ↦ ζ^(jk)` is an
eigenvector of the adjacency matrix with eigenvalue `2 cos (2πk/19)`. -/
theorem huckel_C19_eigenvector (k : Fin 19) :
    C19adj *ᵥ (fun j : Fin 19 => zeta ^ (j.val * k.val))
      = ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ) •
        (fun j : Fin 19 => zeta ^ (j.val * k.val)) := by
  funext j
  have h := congrFun (congrFun C19adj_mul_dftP j) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simpa [Matrix.mulVec, dotProduct, dftP, huckelEigenvalue, mul_comm] using h

/-- The spectrum of the adjacency matrix of `C₁₉` is exactly
`{2 cos (2πk/19) : k = 0, …, 18}`. -/
theorem huckel_C19_spectrum :
    spectrum ℂ C19adj =
      {mu : ℂ | ∃ k : ℕ, k < 19 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)} := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C19]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, Finset.mem_range,
    Set.mem_setOf_eq]

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

