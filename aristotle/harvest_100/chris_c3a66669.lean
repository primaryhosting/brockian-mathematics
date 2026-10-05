import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to come before any other command
(including module doc comments), so the header comment above is placed immediately after
the single `import Mathlib` line; its text is otherwise verbatim.

Mathematical content: the adjacency matrix `C17` of the cycle graph on 17 vertices is the
circulant matrix `A i j = 1` iff `i - j = ±1` (indices in `ZMod 17`).  It is diagonalised by
the discrete Fourier matrix `F i k = ζ^{ik}` (`ζ = exp (2πi/17)`), with eigenvalues
`ζ^k + ζ^{-k} = 2 cos (2πk/17)`.  Hence `det (μ - A) = ∏ (μ - 2 cos (2πk/17))`, and the
spectrum is exactly the set of these 17 numbers.
-/

namespace Chem

open Complex Matrix

/-- A primitive 17-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma hw : IsPrimitiveRoot w 17 := Complex.isPrimitiveRoot_exp 17 (by norm_num)

lemma orderOf_w : orderOf w = 17 := (hw.eq_orderOf).symm

/-- The additive character `m ↦ w ^ m` of `ZMod 17`. -/
noncomputable def zeta (m : ZMod 17) : ℂ := w ^ m.val

/-- The adjacency matrix of the cycle graph `C₁₇`, indexed by `ZMod 17`. -/
def C17 : Matrix (ZMod 17) (ZMod 17) ℂ :=
  fun i j => if i - j = 1 ∨ i - j = -1 then 1 else 0

/-- The claimed eigenvalues `2 cos (2πk/17)`. -/
noncomputable def lam (k : ZMod 17) : ℂ := (2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ)

/-- The (unnormalised) discrete Fourier matrix. -/
noncomputable def F : Matrix (ZMod 17) (ZMod 17) ℂ := fun i k => zeta (i * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def G : Matrix (ZMod 17) (ZMod 17) ℂ := fun k j => zeta (-(j * k)) / 17

lemma w_pow_mod (n : ℕ) : w ^ (n % 17) = w ^ n := by rw [← orderOf_w, pow_mod_orderOf]

lemma zeta_add (a b : ZMod 17) : zeta (a + b) = zeta a * zeta b := by
  unfold zeta
  rw [ZMod.val_add, w_pow_mod, pow_add]

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_ne_zero (a : ZMod 17) : zeta a ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)

lemma zeta_neg (a : ZMod 17) : zeta (-a) = (zeta a)⁻¹ := by
  have h : zeta a * zeta (-a) = 1 := by rw [← zeta_add]; simp [zeta_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma zeta_mul (a b : ZMod 17) : zeta (a * b) = (zeta a) ^ b.val := by
  unfold zeta
  rw [ZMod.val_mul, w_pow_mod, pow_mul]

lemma zeta_sum (m : ZMod 17) : ∑ j : ZMod 17, zeta (j * m) = if m = 0 then 17 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [zeta_zero]
  · simp only [hm, if_false]
    have h1 : ∀ j ∈ (Finset.univ : Finset (ZMod 17)), zeta (j * m) = (zeta m) ^ j.val :=
      fun j _ => by rw [mul_comm, zeta_mul]
    have h2 : ∑ j : ZMod 17, (zeta m) ^ (ZMod.val j) = ∑ i ∈ Finset.range 17, (zeta m) ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (zeta m) ^ i) 17
    rw [Finset.sum_congr rfl h1, h2]
    have hne : m.val ≠ 0 := fun h => hm ((ZMod.val_eq_zero m).mp h)
    have hlt : m.val < 17 := ZMod.val_lt m
    have hnd : ¬ (17 ∣ m.val) := fun hd => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd; omega
    have hcop : Nat.Coprime m.val 17 :=
      Nat.coprime_comm.mp (((by norm_num : Nat.Prime 17).coprime_iff_not_dvd).mpr hnd)
    exact (hw.pow_of_coprime m.val hcop).geom_sum_eq_zero (by norm_num)

lemma zeta_eq_exp (k : ZMod 17) :
    zeta k = Complex.exp ((2 * Real.pi * k.val / 17 : ℝ) * Complex.I) := by
  unfold zeta w
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta_add_zeta_neg (k : ZMod 17) : zeta k + zeta (-k) = lam k := by
  set θ : ℝ := 2 * Real.pi * k.val / 17 with hθ
  rw [zeta_neg, zeta_eq_exp, ← Complex.exp_neg]
  unfold lam
  rw [← hθ]
  push_cast
  rw [Complex.two_cos, neg_mul]

lemma F_mul_G : F * G = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 17, F i k * G k j = zeta (k * (i - j)) / 17 := by
    intro k
    unfold F G
    rw [div_eq_mul_inv, ← mul_assoc, ← zeta_add]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.sum_div, zeta_sum]
  by_cases hij : i = j
  · subst hij; simp
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

lemma C17_mul_F : C17 * F = F * Matrix.diagonal lam := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hstep : ∀ j : ZMod 17, C17 i j * F j k
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 17)) then zeta (j * k) else 0 := by
    intro j
    unfold C17 F
    by_cases h1 : j = i - 1
    · subst h1; simp
    · by_cases h2 : j = i + 1
      · subst h2; simp
      · have hA : ¬ (i - j = 1 ∨ i - j = -1) := by
          rintro (h | h)
          · exact h1 (by linear_combination -h)
          · exact h2 (by linear_combination -h)
        simp [hA, h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]
  rw [Finset.sum_eq_single k]
  · unfold F
    rw [Matrix.diagonal_apply_eq, ← zeta_add_zeta_neg k,
      show (i - 1) * k = i * k + (-k) by ring, show (i + 1) * k = i * k + k by ring,
      zeta_add, zeta_add]
    ring
  · intro b _ hb
    exact mul_eq_zero_of_right _ (Matrix.diagonal_apply_ne _ hb)
  · intro h; simp at h

lemma det_F_mul_det_G : F.det * G.det = 1 := by
  rw [← Matrix.det_mul, F_mul_G, Matrix.det_one]

lemma det_sub (μ : ℂ) :
    (algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - C17).det = ∏ k : ZMod 17, (μ - lam k) := by
  have key : algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - C17
      = F * Matrix.diagonal (fun k => μ - lam k) * G := by
    have h1 : (Matrix.diagonal fun k : ZMod 17 => μ - lam k)
        = algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ - Matrix.diagonal lam := by
      rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
      rfl
    have hc : F * algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ
        = algebraMap ℂ (Matrix (ZMod 17) (ZMod 17) ℂ) μ * F := (Algebra.commutes μ F).symm
    rw [h1, Matrix.mul_sub, hc, ← C17_mul_F, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      F_mul_G, Matrix.mul_one, Matrix.mul_one]
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rw [show F.det * (∏ k : ZMod 17, (μ - lam k)) * G.det
      = (F.det * G.det) * ∏ k : ZMod 17, (μ - lam k) by ring, det_F_mul_det_G, one_mul]

/-- **Hückel theory for the cycle `C₁₇`**: the spectrum of the adjacency matrix of the
cycle graph on 17 vertices is exactly `{2 cos (2πk/17) : k = 0, …, 16}`. -/
theorem huckel_C17 :
    spectrum ℂ C17 =
      Set.range fun k : ZMod 17 => ((2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ) : ℂ) := by
  ext μ
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, det_sub,
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, sub_eq_zero.mpr hk.symm⟩

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

