import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((m + 3 : ℕ) : ℂ))

/-- The characters of `Fin (m+3)`. -/
noncomputable def ee (j : Fin (m + 3)) : ℂ := zeta m ^ (j : ℕ)

/-- The claimed Fiedler value of the cycle `C_{m+3}`. -/
noncomputable def fied : ℝ := 2 - 2 * Real.cos (2 * Real.pi / ((m + 3 : ℕ) : ℝ))

/-- The claimed Fiedler eigenvector. -/
noncomputable def fvec : Fin (m + 3) → ℝ :=
  fun j => Real.cos (2 * Real.pi * (j : ℕ) / ((m + 3 : ℕ) : ℝ))

/-- The discrete Fourier transform on `Fin (m+3)`. -/
noncomputable def dft (y : Fin (m + 3) → ℂ) : Fin (m + 3) → ℂ :=
  fun k => ∑ j : Fin (m + 3), y j * ee m (j * k)

lemma zeta_primitive : IsPrimitiveRoot (zeta m) (m + 3) :=
  Complex.isPrimitiveRoot_exp _ (by omega)

lemma zeta_pow_eq_one : zeta m ^ (m + 3) = 1 := (zeta_primitive m).pow_eq_one

lemma zeta_pow_mod (k : ℕ) : zeta m ^ (k % (m + 3)) = zeta m ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k (m + 3), pow_add, pow_mul, zeta_pow_eq_one, one_pow, one_mul]

lemma ee_zero : ee m 0 = 1 := by
  simp [ee]

lemma ee_add (a b : Fin (m + 3)) : ee m (a + b) = ee m a * ee m b := by
  simp only [ee, Fin.val_add, zeta_pow_mod, pow_add]

lemma ee_ne_zero (a : Fin (m + 3)) : ee m a ≠ 0 := by
  refine pow_ne_zero _ ?_
  simp [zeta, Complex.exp_ne_zero]

lemma ee_eq_one_iff (a : Fin (m + 3)) : ee m a = 1 ↔ a = 0 := by
  rw [ee, (zeta_primitive m).pow_eq_one_iff_dvd]
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  have ha := a.isLt
  refine Fin.ext ?_
  rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0
  · exact h0
  · exact absurd (Nat.le_of_dvd h0 h) (by omega)

lemma norm_ee (a : Fin (m + 3)) : ‖ee m a‖ = 1 := by
  rw [ee, norm_pow, Complex.norm_eq_one_of_pow_eq_one (zeta_pow_eq_one m) (by omega), one_pow]

lemma ee_neg (a : Fin (m + 3)) : ee m (-a) = (starRingEnd ℂ) (ee m a) := by
  have h1 : ee m a * ee m (-a) = 1 := by rw [← ee_add]; simp [ee_zero]
  have h2 : ee m a * (starRingEnd ℂ) (ee m a) = 1 := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, norm_ee]
    norm_num
  exact mul_left_cancel₀ (ee_ne_zero m a) (h1.trans h2.symm)

lemma sum_ee (a : Fin (m + 3)) :
    ∑ j : Fin (m + 3), ee m (a * j) = if a = 0 then ((m + 3 : ℕ) : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [ee_zero]
  · rw [if_neg ha]
    have key : ee m a * ∑ j : Fin (m + 3), ee m (a * j) = ∑ j : Fin (m + 3), ee m (a * j) := by
      rw [Finset.mul_sum,
        ← Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 3))) (fun j => ee m (a * j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.coe_addRight]
      rw [mul_add, ee_add, mul_one, mul_comm]
    have h1 : (ee m a - 1) * ∑ j : Fin (m + 3), ee m (a * j) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) (fun hh => ha ((ee_eq_one_iff m a).1 hh))
    · exact h

lemma ee_eq_exp (k : Fin (m + 3)) :
    ee m k = Complex.exp ((2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ) : ℝ) * Complex.I) := by
  rw [ee, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma normSq_one_sub_ee (k : Fin (m + 3)) :
    Complex.normSq (1 - ee m k)
      = 2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ)) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ) with ht
  rw [ee_eq_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h := Real.sin_sq_add_cos_sq t
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  nlinarith [h]

lemma cos_le_of_ne_zero (k : Fin (m + 3)) (hk : k ≠ 0) :
    Real.cos (2 * Real.pi * (k : ℕ) / ((m + 3 : ℕ) : ℝ))
      ≤ Real.cos (2 * Real.pi / ((m + 3 : ℕ) : ℝ)) := by
  have hpi := Real.pi_pos
  have hklt : (k : ℕ) < m + 3 := k.isLt
  have hk1 : 1 ≤ (k : ℕ) := by
    rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
    · exact absurd (Fin.ext h) hk
    · exact h
  set N : ℝ := ((m + 3 : ℕ) : ℝ) with hNdef
  have hN : (0:ℝ) < N := by rw [hNdef]; positivity
  have hkN : ((k : ℕ) : ℝ) + 1 ≤ N := by rw [hNdef]; exact_mod_cast hklt
  have hk1' : (1:ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk1
  have ha0 : (0:ℝ) ≤ 2 * Real.pi / N := by positivity
  by_cases hc : 2 * ((k : ℕ) : ℝ) ≤ N
  · refine Real.cos_le_cos_of_nonneg_of_le_pi ha0 ?_
      ((div_le_div_iff_of_pos_right hN).mpr (by nlinarith))
    rw [div_le_iff₀ hN]; nlinarith
  · push_neg at hc
    have hcos : Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) / N)
        = Real.cos (2 * Real.pi * (N - ((k : ℕ) : ℝ)) / N) := by
      rw [← Real.cos_two_pi_sub]
      congr 1
      field_simp
    rw [hcos]
    refine Real.cos_le_cos_of_nonneg_of_le_pi ha0 ?_
      ((div_le_div_iff_of_pos_right hN).mpr (by nlinarith))
    rw [div_le_iff₀ hN]; nlinarith

lemma fied_le_normSq (k : Fin (m + 3)) (hk : k ≠ 0) :
    fied m ≤ Complex.normSq (1 - ee m k) := by
  rw [normSq_one_sub_ee, fied]
  have := cos_le_of_ne_zero m k hk
  linarith

lemma fied_pos : 0 < fied m := by
  rw [fied]
  have hpi := Real.pi_pos
  have hN : (0:ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  have h3 : (3:ℝ) ≤ ((m + 3 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  have h1 : 0 < 2 * Real.pi / ((m + 3 : ℕ) : ℝ) := by positivity
  have h2 : 2 * Real.pi / ((m + 3 : ℕ) : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hN]; nlinarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) h2 h1
  simp only [Real.cos_zero] at this
  linarith

lemma parseval (y : Fin (m + 3) → ℂ) :
    ∑ k : Fin (m + 3), Complex.normSq (dft m y k)
      = ((m + 3 : ℕ) : ℝ) * ∑ j : Fin (m + 3), Complex.normSq (y j) := by
  have key : ∀ k : Fin (m + 3), dft m y k * (starRingEnd ℂ) (dft m y k)
      = ∑ j : Fin (m + 3), ∑ l : Fin (m + 3),
          y j * (starRingEnd ℂ) (y l) * ee m ((j - l) * k) := by
    intro k
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← ee_neg]
    have hd : (j - l) * k = j * k + (-(l * k)) := by rw [sub_mul, sub_eq_add_neg]
    rw [hd, ee_add]
    ring
  have main : ∑ k : Fin (m + 3), dft m y k * (starRingEnd ℂ) (dft m y k)
      = ((m + 3 : ℕ) : ℂ) * ∑ j : Fin (m + 3), y j * (starRingEnd ℂ) (y j) := by
    simp_rw [key]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have hin : ∀ l : Fin (m + 3),
        ∑ k : Fin (m + 3), y j * (starRingEnd ℂ) (y l) * ee m ((j - l) * k)
          = y j * (starRingEnd ℂ) (y l) * (if l = j then ((m + 3 : ℕ) : ℂ) else 0) := by
      intro l
      rw [← Finset.mul_sum, sum_ee]
      congr 1
      by_cases h : l = j
      · simp [h]
      · rw [if_neg h, if_neg]
        exact fun hc => h (sub_eq_zero.1 hc).symm
    rw [Finset.sum_congr rfl (fun l _ => hin l)]
    simp [Finset.sum_ite_eq' Finset.univ j]
    ring
  have hL : ∑ k : Fin (m + 3), dft m y k * (starRingEnd ℂ) (dft m y k)
      = ((∑ k : Fin (m + 3), Complex.normSq (dft m y k) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => Complex.mul_conj _
  have hR : ∑ j : Fin (m + 3), y j * (starRingEnd ℂ) (y j)
      = ((∑ j : Fin (m + 3), Complex.normSq (y j) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun j _ => Complex.mul_conj _
  rw [hL, hR] at main
  exact_mod_cast main

lemma dft_shift (x : Fin (m + 3) → ℂ) (k : Fin (m + 3)) :
    dft m (fun j => x j - x (j + 1)) k = (1 - ee m (-k)) * dft m x k := by
  have hre : ∑ j : Fin (m + 3), x (j + 1) * ee m (j * k)
      = ee m (-k) * ∑ j : Fin (m + 3), x j * ee m (j * k) := by
    have h1 : ∑ j : Fin (m + 3), x (j + 1) * ee m ((j + 1 - 1) * k)
        = ∑ j : Fin (m + 3), x j * ee m ((j - 1) * k) :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 3))) (fun j => x j * ee m ((j - 1) * k))
    simp only [add_sub_cancel_right] at h1
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd : (j - 1) * k = j * k + (-k) := by rw [sub_mul, sub_eq_add_neg, one_mul]
    rw [hd, ee_add]
    ring
  simp only [dft, sub_mul, Finset.sum_sub_distrib, hre]
  ring

/-- The discrete Wirtinger inequality for the cycle. -/
lemma wirtinger (x : Fin (m + 3) → ℝ) (hx : ∑ i : Fin (m + 3), x i = 0) :
    fied m * ∑ i : Fin (m + 3), (x i) ^ 2 ≤ ∑ i : Fin (m + 3), (x i - x (i + 1)) ^ 2 := by
  set y : Fin (m + 3) → ℂ := fun j => (x j : ℂ) with hy
  have hy0 : dft m y 0 = 0 := by
    rw [dft]
    have h2 : ∀ j : Fin (m + 3), y j * ee m (j * 0) = y j := by
      intro j; rw [mul_zero, ee_zero, mul_one]
    rw [Finset.sum_congr rfl (fun j _ => h2 j), hy]
    rw [← Complex.ofReal_sum, hx, Complex.ofReal_zero]
  have hterm : ∀ k : Fin (m + 3),
      fied m * Complex.normSq (dft m y k)
        ≤ Complex.normSq (dft m (fun j => y j - y (j + 1)) k) := by
    intro k
    rw [dft_shift, Complex.normSq_mul]
    by_cases hk : k = 0
    · subst hk; rw [hy0]; simp
    · have h1 : fied m ≤ Complex.normSq (1 - ee m (-k)) :=
        fied_le_normSq m (-k) (neg_ne_zero.2 hk)
      nlinarith [Complex.normSq_nonneg (dft m y k), Complex.normSq_nonneg (1 - ee m (-k))]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [← Finset.mul_sum, parseval, parseval] at hsum
  have hN : (0:ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  have e1 : ∀ j : Fin (m + 3), Complex.normSq (y j) = (x j) ^ 2 := by
    intro j; rw [hy]; simp [Complex.normSq_ofReal]; ring
  have e2 : ∀ j : Fin (m + 3), Complex.normSq (y j - y (j + 1)) = (x j - x (j + 1)) ^ 2 := by
    intro j
    have h3 : y j - y (j + 1) = ((x j - x (j + 1) : ℝ) : ℂ) := by rw [hy]; push_cast; ring
    rw [h3, Complex.normSq_ofReal]; ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_congr rfl (fun j _ => e2 j)] at hsum
  nlinarith [hsum]

lemma lap_mulVec (x : Fin (m + 3) → ℝ) (i : Fin (m + 3)) :
    ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i = 2 * x i - x (i - 1) - x (i + 1) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  have hd : (SimpleGraph.cycleGraph (m + 3)).degree i = 2 := SimpleGraph.cycleGraph_degree_three_le
  have hn : (SimpleGraph.cycleGraph (m + 3)).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset
  have hne : i - 1 ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  rw [hd, hn, Finset.sum_pair hne]
  push_cast
  ring

lemma shift_sum (f : Fin (m + 3) → ℝ) : ∑ i, f (i + 1) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 3))) f

lemma shift_sum' (f : Fin (m + 3) → ℝ) : ∑ i, f (i - 1) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.subRight (1 : Fin (m + 3))) f

lemma dot_lap (x : Fin (m + 3) → ℝ) :
    x ⬝ᵥ ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
      = ∑ i : Fin (m + 3), (x i - x (i + 1)) ^ 2 := by
  have h1 : ∑ i : Fin (m + 3), x (i + 1) ^ 2 = ∑ i : Fin (m + 3), x i ^ 2 :=
    shift_sum m (fun j => x j ^ 2)
  have h2 : ∑ i : Fin (m + 3), x (i + 1) * x (i + 1 - 1) = ∑ i : Fin (m + 3), x i * x (i - 1) :=
    shift_sum m (fun j => x j * x (j - 1))
  simp only [add_sub_cancel_right] at h2
  simp only [dotProduct, lap_mulVec]
  have hexp : ∀ i : Fin (m + 3), x i * (2 * x i - x (i - 1) - x (i + 1))
      = 2 * x i ^ 2 - x i * x (i - 1) - x i * x (i + 1) := fun i => by ring
  simp only [hexp, Finset.sum_sub_distrib]
  have h3 : ∀ i : Fin (m + 3), (x i - x (i + 1)) ^ 2
      = x i ^ 2 + x (i + 1) ^ 2 - 2 * (x i * x (i + 1)) := fun i => by ring
  simp only [h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1]
  have h4 : ∑ i : Fin (m + 3), x i * x (i - 1) = ∑ i : Fin (m + 3), x i * x (i + 1) := by
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  ring

lemma cos_mod (k : ℕ) :
    Real.cos (2 * Real.pi * ((k % (m + 3) : ℕ) : ℝ) / ((m + 3 : ℕ) : ℝ))
      = Real.cos (2 * Real.pi * (k : ℝ) / ((m + 3 : ℕ) : ℝ)) := by
  have hN : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hk : (k : ℝ) = ((m + 3 : ℕ) : ℝ) * ((k / (m + 3) : ℕ) : ℝ) + ((k % (m + 3) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.div_add_mod k (m + 3)).symm
  rw [hk]
  have hsplit : 2 * Real.pi * (((m + 3 : ℕ) : ℝ) * ((k / (m + 3) : ℕ) : ℝ)
        + ((k % (m + 3) : ℕ) : ℝ)) / ((m + 3 : ℕ) : ℝ)
      = 2 * Real.pi * ((k % (m + 3) : ℕ) : ℝ) / ((m + 3 : ℕ) : ℝ)
        + ((k / (m + 3) : ℕ) : ℝ) * (2 * Real.pi) := by
    field_simp
    ring
  rw [hsplit, Real.cos_add_nat_mul_two_pi]

lemma fvec_apply (i : Fin (m + 3)) (k : ℕ) (h : (i : ℕ) = k % (m + 3)) :
    fvec m i = Real.cos (2 * Real.pi * (k : ℝ) / ((m + 3 : ℕ) : ℝ)) := by
  rw [fvec, h, cos_mod]

lemma fvec_succ (i : Fin (m + 3)) :
    fvec m (i + 1) = Real.cos (2 * Real.pi * (i : ℕ) / ((m + 3 : ℕ) : ℝ)
      + 2 * Real.pi / ((m + 3 : ℕ) : ℝ)) := by
  have hN : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fvec_apply m (i + 1) ((i : ℕ) + 1) (by rw [Fin.val_add, Fin.val_one])]
  congr 1
  push_cast
  field_simp

lemma fvec_pred (i : Fin (m + 3)) :
    fvec m (i - 1) = Real.cos (2 * Real.pi * (i : ℕ) / ((m + 3 : ℕ) : ℝ)
      - 2 * Real.pi / ((m + 3 : ℕ) : ℝ)) := by
  have hN : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fvec_apply m (i - 1) (m + 3 - 1 + (i : ℕ)) (by rw [Fin.sub_def, Fin.val_one])]
  have hc : ((m + 3 - 1 + (i : ℕ) : ℕ) : ℝ) = ((m + 3 : ℕ) : ℝ) - 1 + ((i : ℕ) : ℝ) := by
    have h1 : ((m + 3 - 1 : ℕ) : ℝ) = ((m + 3 : ℕ) : ℝ) - 1 :=
      Nat.cast_sub (by omega) |>.trans (by norm_num)
    push_cast [h1]
    ring
  rw [hc]
  have hsplit : 2 * Real.pi * (((m + 3 : ℕ) : ℝ) - 1 + ((i : ℕ) : ℝ)) / ((m + 3 : ℕ) : ℝ)
      = (2 * Real.pi * ((i : ℕ) : ℝ) / ((m + 3 : ℕ) : ℝ)
        - 2 * Real.pi / ((m + 3 : ℕ) : ℝ)) + 2 * Real.pi := by
    field_simp
    ring
  rw [hsplit, Real.cos_add_two_pi]

lemma fvec_ne_zero : fvec m ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [fvec] at h0

lemma fvec_eq_re (j : Fin (m + 3)) : fvec m j = (ee m j).re := by
  rw [ee_eq_exp, Complex.exp_ofReal_mul_I_re, fvec]

lemma fvec_sum_zero : ∑ i : Fin (m + 3), fvec m i = 0 := by
  have h1 : ∑ i : Fin (m + 3), fvec m i = (∑ i : Fin (m + 3), ee m ((1 : Fin (m + 3)) * i)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [one_mul, fvec_eq_re]
  rw [h1, sum_ee, if_neg]
  · simp
  · simp

lemma fvec_eigen :
    (SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fvec m = fied m • fvec m := by
  funext i
  rw [lap_mulVec, fvec_succ, fvec_pred, Pi.smul_apply, smul_eq_mul, fied, fvec,
    Real.cos_add, Real.cos_sub]
  ring

lemma dotProduct_pos {x : Fin (m + 3) → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hx

/-- Any eigenvector for a nonzero eigenvalue of the cycle Laplacian sums to zero. -/
lemma sum_eq_zero_of_eigen {μ : ℝ} (hμ : μ ≠ 0) {x : Fin (m + 3) → ℝ}
    (hx : (SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x = μ • x) :
    ∑ i : Fin (m + 3), x i = 0 := by
  have hsum : ∑ i : Fin (m + 3), ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i
      = μ * ∑ i : Fin (m + 3), x i := by
    rw [hx]
    simp [Finset.mul_sum]
  rw [show (∑ i : Fin (m + 3), ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i)
      = ∑ i : Fin (m + 3), (2 * x i - x (i - 1) - x (i + 1)) from
    Finset.sum_congr rfl fun i _ => lap_mulVec m x i] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, shift_sum m x,
    shift_sum' m x] at hsum
  have hz : μ * ∑ i : Fin (m + 3), x i = 0 := by linarith
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h hμ
  · exact h

end CycleAux

open CycleAux in
/-- **Fiedler value of the cycle graph.**  For `n ≥ 3` the algebraic connectivity of the cycle
`C n` equals `2 - 2 cos (2π/n)`: it is the least Rayleigh quotient of the Laplacian over nonzero
vectors orthogonal to the all-ones vector, and equivalently the least nonzero eigenvalue of the
Laplacian. -/
theorem cycle_fiedler_value (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {μ : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (∑ i, x i) = 0 ∧
        μ = (x ⬝ᵥ ((SimpleGraph.cycleGraph n).lapMatrix ℝ *ᵥ x)) / (x ⬝ᵥ x)}
      (2 - 2 * Real.cos (2 * Real.pi / (n : ℝ)))
    ∧ IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ x : Fin n → ℝ, x ≠ 0 ∧
        (SimpleGraph.cycleGraph n).lapMatrix ℝ *ᵥ x = μ • x}
      (2 - 2 * Real.cos (2 * Real.pi / (n : ℝ))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hfied : (2 : ℝ) - 2 * Real.cos (2 * Real.pi / ((m + 3 : ℕ) : ℝ)) = fied m := rfl
  rw [hfied]
  refine ⟨⟨⟨fvec m, fvec_ne_zero m, fvec_sum_zero m, ?_⟩, ?_⟩, ⟨⟨(fied_pos m).ne', fvec m,
    fvec_ne_zero m, fvec_eigen m⟩, ?_⟩⟩
  · rw [fvec_eigen m, dotProduct_smul, smul_eq_mul,
      mul_div_assoc, div_self (dotProduct_pos m (fvec_ne_zero m)).ne', mul_one]
  · rintro μ ⟨x, hx0, hxsum, rfl⟩
    rw [le_div_iff₀ (dotProduct_pos m hx0), dot_lap]
    have h := wirtinger m x hxsum
    have : x ⬝ᵥ x = ∑ i : Fin (m + 3), (x i) ^ 2 := by
      simp [dotProduct, sq]
    rw [this]
    linarith
  · rintro μ ⟨hμ0, x, hx0, hx⟩
    have hsum := sum_eq_zero_of_eigen m hμ0 hx
    have h := wirtinger m x hsum
    have hdot : x ⬝ᵥ ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
        = μ * ∑ i : Fin (m + 3), (x i) ^ 2 := by
      rw [hx, dotProduct_smul, smul_eq_mul]
      simp [dotProduct, sq]
    rw [dot_lap] at hdot
    have hpos : 0 < ∑ i : Fin (m + 3), (x i) ^ 2 := by
      have := dotProduct_pos m hx0
      have heq : x ⬝ᵥ x = ∑ i : Fin (m + 3), (x i) ^ 2 := by simp [dotProduct, sq]
      linarith [heq ▸ this]
    nlinarith [h, hdot]

end Frontier.Spectral

