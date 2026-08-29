/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₉`

We show that the spectrum of the adjacency matrix of the cycle graph `C₁₉`
(the Hückel matrix of the annulene `C₁₉` in units where `α = 0`, `β = 1`)
is exactly `{2 cos (2πk/19) : k = 0, …, 18}`.

The proof diagonalizes the circulant adjacency matrix by the discrete Fourier matrix.
-/

namespace Chem

open Complex Matrix Finset

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- A primitive 19-th root of unity. -/
noncomputable def w19 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

lemma isPrimitiveRoot_w19 : IsPrimitiveRoot w19 19 := by
  have h := Complex.isPrimitiveRoot_exp 19 (by norm_num)
  simpa [w19] using h

lemma w19_pow_19 : w19 ^ 19 = 1 := isPrimitiveRoot_w19.pow_eq_one

/-- The character `k ↦ ω^k` of `ZMod 19`. -/
noncomputable def ee (a : ZMod 19) : ℂ := w19 ^ a.val

lemma w19_pow_mod (x : ℕ) : w19 ^ (x % 19) = w19 ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 19]
  rw [pow_add, pow_mul, w19_pow_19, one_pow, one_mul]

lemma ee_add (a b : ZMod 19) : ee (a + b) = ee a * ee b := by
  simp only [ee, ZMod.val_add, w19_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (a : ZMod 19) : ee a ≠ 0 := by
  have h : ee a * ee (-a) = 1 := by rw [← ee_add]; simp [ee_zero]
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

lemma ee_neg (a : ZMod 19) : ee (-a) = (ee a)⁻¹ := by
  have h : ee a * ee (-a) = 1 := by rw [← ee_add]; simp [ee_zero]
  have ha := ee_ne_zero a
  field_simp
  linear_combination h

lemma ee_sub (a b : ZMod 19) : ee (a - b) = ee a * ee (-b) := by
  rw [sub_eq_add_neg, ee_add]

/-- The adjacency matrix of the cycle graph `C₁₉`, with vertices indexed by `ZMod 19`:
two vertices are adjacent iff they differ by `1`. -/
def C19adj : Matrix (ZMod 19) (ZMod 19) ℂ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/19)`. -/
noncomputable def mu (k : ZMod 19) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)

/-- The discrete Fourier matrix of `ZMod 19`. -/
noncomputable def Fm : Matrix (ZMod 19) (ZMod 19) ℂ := fun i j => ee (i * j)

/-- The inverse discrete Fourier matrix of `ZMod 19`. -/
noncomputable def Gm : Matrix (ZMod 19) (ZMod 19) ℂ := fun i j => (19 : ℂ)⁻¹ * ee (-(i * j))

lemma sum_ee : ∑ k : ZMod 19, ee k = 0 := by
  have h : ∑ k : ZMod 19, ee k = ∑ n ∈ Finset.range 19, w19 ^ n := by
    show ∑ k : Fin 19, w19 ^ (k : ℕ) = _
    exact Fin.sum_univ_eq_sum_range (fun n => w19 ^ n) 19
  rw [h, isPrimitiveRoot_w19.geom_sum_eq_zero (by norm_num)]

lemma sum_ee_mul (c : ZMod 19) : ∑ k : ZMod 19, ee (k * c) = if c = 0 then 19 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ee_zero, Finset.card_univ]
  · simp only [hc, if_false]
    have h2 : ∑ k : ZMod 19, ee (k * c) = ∑ k : ZMod 19, ee k :=
      Fintype.sum_equiv (Equiv.mulRight₀ c hc) _ _ (fun x => by simp [Equiv.mulRight₀])
    rw [h2, sum_ee]

lemma Fm_mul_Gm : Fm * Gm = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 19, Fm i k * Gm k j = (19 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    simp only [Fm, Gm]
    rw [show k * (i - j) = i * k - k * j by ring, ee_sub]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_ee_mul]
  rcases eq_or_ne i j with hij | hij
  · subst hij
    simp [Matrix.one_apply_eq]
  · rw [if_neg (sub_ne_zero_of_ne hij)]
    simp [hij]

lemma Gm_mul_Fm : Gm * Fm = 1 := mul_eq_one_comm.mp Fm_mul_Gm

lemma ee_eq_exp (k : ZMod 19) : ee k = Complex.exp ((2 * Real.pi * k.val / 19 : ℝ) * I) := by
  rw [ee, w19, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma ee_add_ee_neg (k : ZMod 19) : ee k + ee (-k) = mu k := by
  have hcos : ∀ z : ℂ, Complex.exp (z * I) + Complex.exp (-z * I) = 2 * Complex.cos z := by
    intro z
    rw [Complex.cos]
    ring
  have h1 : ee (-k) = Complex.exp (-(2 * Real.pi * k.val / 19 : ℝ) * I) := by
    rw [ee_neg, ee_eq_exp, ← Complex.exp_neg]
    ring_nf
  rw [ee_eq_exp, h1, hcos, mu]
  push_cast
  ring

lemma C19adj_apply (i k : ZMod 19) :
    C19adj i k = (if k = i + 1 then (1 : ℂ) else 0) + (if k = i - 1 then 1 else 0) := by
  have key : (i - k = 1 ∨ k - i = 1) ↔ (k = i + 1 ∨ k = i - 1) := by
    constructor
    · rintro (h | h)
      · right; rw [← h]; ring
      · left; rw [← h]; ring
    · rintro (h | h) <;> subst h <;> [right; left] <;> ring
  have hne : (i + 1 : ZMod 19) ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 19) = 0 := by linear_combination h
    revert h2; decide
  simp only [C19adj, key]
  by_cases h1 : k = i + 1
  · subst h1; simp [hne]
  · by_cases h2 : k = i - 1 <;> simp [h1, h2, Ne.symm hne]

lemma C19adj_mul_Fm : C19adj * Fm = Fm * diagonal mu := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 19, C19adj i k * Fm k j
      = (if k = i + 1 then ee (k * j) else 0) + (if k = i - 1 then ee (k * j) else 0) := by
    intro k
    rw [C19adj_apply]
    simp only [Fm, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun k => ee (k * j)),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun k => ee (k * j))]
  simp only [Finset.mem_univ, if_true]
  rw [Matrix.mul_diagonal]
  rw [show (i + 1) * j = i * j + j by ring, show (i - 1) * j = i * j + (-j) by ring,
    ee_add, ee_add, ← mul_add, ee_add_ee_neg]
  rfl

lemma C19adj_eq : C19adj = Fm * diagonal mu * Gm := by
  rw [← C19adj_mul_Fm, Matrix.mul_assoc, Fm_mul_Gm, Matrix.mul_one]

lemma det_Fm_mul_det_Gm : Fm.det * Gm.det = 1 := by
  rw [← Matrix.det_mul, Fm_mul_Gm, Matrix.det_one]

lemma det_sub (z : ℂ) :
    ((algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ)) z - C19adj).det
      = ∏ k : ZMod 19, (z - mu k) := by
  have hz : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ)) z
      = Fm * diagonal (fun _ : ZMod 19 => z) * Gm := by
    have hd : (diagonal (fun _ : ZMod 19 => z)) = z • (1 : Matrix (ZMod 19) (ZMod 19) ℂ) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Fm_mul_Gm,
      Algebra.algebraMap_eq_smul_one]
  have hdiff : (algebraMap ℂ (Matrix (ZMod 19) (ZMod 19) ℂ)) z - C19adj
      = Fm * diagonal (fun k : ZMod 19 => z - mu k) * Gm := by
    rw [hz, C19adj_eq, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
  rw [hdiff, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rw [mul_comm Fm.det _, mul_assoc, det_Fm_mul_det_Gm, mul_one]

/-- **Hückel spectrum of the cycle `C₁₉`.**  The eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)` for `k = 0, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ C19adj =
      {z : ℂ | ∃ k : ℕ, k < 19 ∧ z = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, det_sub, isUnit_iff_ne_zero,
    not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have : z = mu k := sub_eq_zero.mp hk
    rw [this, mu]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨(n : ZMod 19), Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, mu, ZMod.val_natCast_of_lt hn]

/-- Auxiliary cancellation lemma. -/
theorem mul_mid_mul_of_mul_eq_one {R : Type*} [CommRing R] {a b p : R} (h : a * b = 1) :
    a * p * b = p := by
  rw [mul_comm a p, mul_assoc, h, mul_one]

lemma det_diagonal_charpoly_factors :
    (diagonal (fun k : ZMod 19 => Polynomial.X - Polynomial.C (mu k))).det
      = ∏ k : ZMod 19, (Polynomial.X - Polynomial.C (mu k)) := by
  rw [Matrix.det_diagonal]

/-- The characteristic polynomial of the adjacency matrix of `C₁₉` factors as
`∏_{k=0}^{18} (X - 2 cos (2πk/19))`; in particular the `19` eigenvalues, counted with
multiplicity, are the numbers `2 cos (2πk/19)`, `k = 0, …, 18`. -/
theorem huckel_C19_charpoly :
    C19adj.charpoly = ∏ k : ZMod 19, (Polynomial.X - Polynomial.C (mu k)) := by
  set FC : Matrix (ZMod 19) (ZMod 19) (Polynomial ℂ) := Fm.map Polynomial.C with hFC
  set GC : Matrix (ZMod 19) (ZMod 19) (Polynomial ℂ) := Gm.map Polynomial.C with hGC
  have hFG : FC * GC = 1 := by
    rw [hFC, hGC, ← Matrix.map_mul, Fm_mul_Gm, Matrix.map_one] <;> simp
  have hscalar : (Matrix.scalar (ZMod 19)) (Polynomial.X : (Polynomial ℂ))
      = FC * diagonal (fun _ : ZMod 19 => (Polynomial.X : (Polynomial ℂ))) * GC := by
    have hd : (diagonal (fun _ : ZMod 19 => (Polynomial.X : (Polynomial ℂ))))
        = (Polynomial.X : (Polynomial ℂ)) • (1 : Matrix (ZMod 19) (ZMod 19) (Polynomial ℂ)) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hFG]
    ext a b
    by_cases h : a = b <;> simp [h]
  have hmapA : C19adj.map Polynomial.C
      = FC * diagonal (fun k : ZMod 19 => Polynomial.C (mu k)) * GC := by
    rw [hFC, hGC, C19adj_eq, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (by simp)]
  have hchar : charmatrix C19adj
      = FC * diagonal (fun k : ZMod 19 => Polynomial.X - Polynomial.C (mu k)) * GC := by
    rw [charmatrix, RingHom.mapMatrix_apply, hscalar, hmapA, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.diagonal_sub]
  have hdet : FC.det * GC.det = 1 := by rw [← Matrix.det_mul, hFG, Matrix.det_one]
  have e1 : C19adj.charpoly
      = FC.det * (diagonal (fun k : ZMod 19 => Polynomial.X - Polynomial.C (mu k))).det * GC.det := by
    rw [Matrix.charpoly, hchar, Matrix.det_mul, Matrix.det_mul]
  rw [e1, det_diagonal_charpoly_factors]
  exact mul_mid_mul_of_mul_eq_one hdet

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

