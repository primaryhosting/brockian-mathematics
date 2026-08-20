/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

/-- The adjacency matrix of the cycle graph `C₁₉`, with vertices indexed by `ZMod 19`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/
def C19adj : Matrix (ZMod 19) (ZMod 19) ℂ :=
  fun i j => (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0)

/-- The Hückel eigenvalues `2 cos (2πk/19)`. -/
noncomputable def C19eig (k : ZMod 19) : ℂ := 2 * (Real.cos (2 * Real.pi * k.val / 19) : ℝ)

/-- The discrete Fourier matrix, whose columns are the eigenvectors of `C19adj`. -/
noncomputable def C19vec : Matrix (ZMod 19) (ZMod 19) ℂ := fun i k => om ^ (i.val * k.val)

/-- The (unnormalised) inverse Fourier matrix. -/
noncomputable def C19conj : Matrix (ZMod 19) (ZMod 19) ℂ := fun k j => om ^ (18 * (k.val * j.val))

/-! ### Basic facts about the root of unity -/

lemma om_prim : IsPrimitiveRoot om 19 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 19 (by norm_num)

lemma om_pow_19 : om ^ 19 = 1 := om_prim.pow_eq_one

lemma om_pow_congr {a b : ℕ} (h : a % 19 = b % 19) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 19]
  conv_rhs => rw [← Nat.div_add_mod b 19]
  simp [pow_add, pow_mul, om_pow_19, h]

lemma om_pow_eq_exp (m : ℕ) :
    om ^ m = Complex.exp (((2 * Real.pi * m / 19 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma exp_two_pi_nat (m : ℕ) : Complex.exp ((2 * Real.pi * m : ℂ) * Complex.I) = 1 := by
  rw [show ((2 * Real.pi * m : ℂ) * Complex.I) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

/-- `ω^m + ω^(18m) = 2 cos (2πm/19)`, the eigenvalue attached to the `m`-th Fourier mode. -/
lemma om_pow_add (m : ℕ) :
    om ^ m + om ^ (18 * m) = 2 * (Real.cos (2 * Real.pi * m / 19) : ℝ) := by
  have key : ((2 * Real.pi * ((18 * m : ℕ) : ℝ) / 19 : ℝ) : ℂ) * Complex.I
      = (2 * Real.pi * m : ℂ) * Complex.I + ((-(2 * Real.pi * m / 19 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have h1 : om ^ (18 * m) = Complex.exp ((-(2 * Real.pi * m / 19 : ℝ) : ℂ) * Complex.I) := by
    rw [om_pow_eq_exp, key, Complex.exp_add, exp_two_pi_nat, one_mul]
  rw [om_pow_eq_exp, h1, Complex.ofReal_cos, Complex.two_cos]

/-! ### The Fourier matrix diagonalises the adjacency matrix -/

lemma val_modeq (i : ZMod 19) (c : ℕ) : (i + (c : ZMod 19)).val ≡ i.val + c [MOD 19] := by
  rw [Nat.ModEq, ZMod.val_add, ZMod.val_natCast]
  omega

lemma om_shift (i : ZMod 19) (c m : ℕ) :
    om ^ ((i + (c : ZMod 19)).val * m) = om ^ ((i.val + c) * m) :=
  om_pow_congr (Nat.ModEq.mul_right m (val_modeq i c))

/-- The eigenvalue equation `A · V = V · diag(λ)`. -/
lemma adj_mul_vec : C19adj * C19vec = C19vec * Matrix.diagonal C19eig := by
  ext i k
  have h1 : (C19adj * C19vec) i k = om ^ ((i + 1).val * k.val) + om ^ ((i - 1).val * k.val) := by
    simp [Matrix.mul_apply, C19adj, C19vec, add_mul, Finset.sum_add_distrib]
  have e1 : i + 1 = i + ((1 : ℕ) : ZMod 19) := by norm_num
  have e2 : i - 1 = i + ((18 : ℕ) : ZMod 19) := by
    rw [sub_eq_add_neg]
    norm_num
    decide
  rw [h1, e1, e2, om_shift, om_shift, Matrix.mul_diagonal]
  show om ^ ((i.val + 1) * k.val) + om ^ ((i.val + 18) * k.val)
      = om ^ (i.val * k.val) * C19eig k
  rw [C19eig, ← om_pow_add k.val, add_mul, add_mul, pow_add, pow_add, mul_add]
  ring_nf

/-- The Fourier matrix is invertible: `V · V̄ = 19 · I`. -/
lemma vec_mul_conj : C19vec * C19conj = (19 : ℂ) • (1 : Matrix (ZMod 19) (ZMod 19) ℂ) := by
  ext i j
  set c : ℕ := (i.val + 18 * j.val) % 19 with hc
  set z : ℂ := om ^ c with hz
  have hterm : ∀ k : ZMod 19, C19vec i k * C19conj k j = z ^ k.val := by
    intro k
    rw [C19vec, C19conj, hz, ← pow_mul, ← pow_add]
    refine om_pow_congr ?_
    have hmod : c * k.val % 19 = ((i.val + 18 * j.val) * k.val) % 19 := by
      simp [hc, Nat.mul_mod]
    rw [hmod]
    congr 1
    ring
  have hsum : (C19vec * C19conj) i j = ∑ m ∈ Finset.range 19, z ^ m := by
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => hterm k)]
    exact Fin.sum_univ_eq_sum_range (fun m => z ^ m) 19
  rw [hsum]
  by_cases h : i = j
  · subst h
    have hc0 : c = 0 := by
      have := i.val_lt
      omega
    simp [hz, hc0]
  · have hcne : c ≠ 0 := by
      intro h0
      apply h
      apply ZMod.val_injective 19
      have hi := i.val_lt
      have hj := j.val_lt
      rw [hc] at h0
      omega
    have hzne : z ≠ 1 := om_prim.pow_ne_one_of_pos_of_lt hcne (by simp [hc]; omega)
    have hz19 : z ^ 19 = 1 := by
      rw [hz, ← pow_mul, mul_comm, pow_mul, om_pow_19, one_pow]
    rw [geom_sum_eq hzne, hz19, sub_self, zero_div]
    simp [h]

lemma det_vec_ne_zero : C19vec.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det vec_mul_conj
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, ZMod.card] at h
  norm_num at h

/-! ### The characteristic determinant -/

lemma det_sub (mu : ℂ) :
    (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj).det
      = ∏ k : ZMod 19, (mu - C19eig k) := by
  have hdiag : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu) - Matrix.diagonal C19eig
      = Matrix.diagonal (fun k => mu - C19eig k) := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
    split <;> simp
  have hcomm : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu) * C19vec
      = C19vec * (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu) :=
    Algebra.commutes mu C19vec
  have hmul : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj) * C19vec
      = C19vec * Matrix.diagonal (fun k => mu - C19eig k) := by
    rw [← hdiag, Matrix.sub_mul, Matrix.mul_sub, hcomm, adj_mul_vec]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ det_vec_ne_zero (by rw [hdet]; ring :
    (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj).det * C19vec.det
      = (∏ k : ZMod 19, (mu - C19eig k)) * C19vec.det)
  exact this

/-! ### Main theorem -/

/-- **Hückel theory for `C₁₉`.** The eigenvalues (spectrum) of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)` for `k = 0, 1, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ C19adj =
      {mu : ℂ | ∃ k : ℕ, k < 19 ∧ mu = 2 * Real.cos (2 * Real.pi * k / 19)} := by
  ext mu
  have hmem : mu ∈ spectrum ℂ C19adj ↔
      (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ) mu - C19adj).det = 0 := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  rw [hmem, det_sub, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k.val, k.val_lt, ?_⟩
    have : mu = C19eig k := by linear_combination hk
    rw [this, C19eig]
  · rintro ⟨k, hk, hmu⟩
    refine ⟨(k : ZMod 19), Finset.mem_univ _, ?_⟩
    rw [C19eig, ZMod.val_natCast_of_lt hk, hmu]
    push_cast
    ring

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

