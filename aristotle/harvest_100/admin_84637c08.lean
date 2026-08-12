/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma zeta_primitive (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma zeta_pow_N (hN : N ≠ 0) : (zeta N) ^ N = 1 := (zeta_primitive hN).pow_eq_one

lemma zeta_pow_mod (hN : N ≠ 0) (x : ℕ) : (zeta N) ^ (x % N) = (zeta N) ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x N, pow_add, pow_mul, zeta_pow_N hN, one_pow, one_mul]

/-- The standard additive character `a ↦ exp (2πi a / N)` on `ZMod N`. -/
noncomputable def chi (N : ℕ) (a : ZMod N) : ℂ := (zeta N) ^ (a.val)

lemma chi_add [NeZero N] (a b : ZMod N) : chi N (a + b) = chi N a * chi N b := by
  simp only [chi, ZMod.val_add, ← pow_add]
  exact zeta_pow_mod (NeZero.ne N) _

lemma chi_zero [NeZero N] : chi N 0 = 1 := by simp [chi]

lemma chi_norm [NeZero N] (a : ZMod N) : ‖chi N a‖ = 1 := by
  simp [chi, norm_pow, Complex.norm_exp, zeta]

lemma chi_normSq [NeZero N] (a : ZMod N) : normSq (chi N a) = 1 := by
  exact Real.sqrt_eq_one.mp (chi_norm (N := N) a)

lemma chi_ne_one [NeZero N] {a : ZMod N} (ha : a ≠ 0) : chi N a ≠ 1 :=
  (zeta_primitive (NeZero.ne N)).pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero a).mpr ha) a.val_lt

lemma chi_conj [NeZero N] (a : ZMod N) : conj (chi N a) = chi N (-a) := by
  rw [← inv_eq_conj (chi_norm a)]
  exact inv_eq_of_mul_eq_one_right (by rw [← chi_add, add_neg_cancel, chi_zero])

lemma chi_re [NeZero N] (a : ZMod N) :
    (chi N a).re = Real.cos (2 * Real.pi * a.val / N) := by
  rw [chi, zeta, ← Complex.exp_nat_mul,
    show (a.val : ℂ) * (2 * Real.pi * Complex.I / N)
      = ((2 * Real.pi * a.val / N : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- Orthogonality of characters. -/
lemma sum_chi [NeZero N] (t : ZMod N) :
    ∑ k : ZMod N, chi N (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht, chi_zero, Finset.card_univ, ZMod.card]
  · have key : chi N t * ∑ k : ZMod N, chi N (t * k) = ∑ k : ZMod N, chi N (t * k) := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _
        (fun k => by simp only [Equiv.coe_addRight, mul_add, mul_one, chi_add]; ring)
    have h2 : (chi N t - 1) * ∑ k : ZMod N, chi N (t * k) = 0 := by linear_combination key
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (by linear_combination h) (chi_ne_one ht)
    · exact h

/-- Parseval's identity for the discrete Fourier transform on `ZMod N`. -/
lemma parseval [NeZero N] (x : ZMod N → ℂ) :
    ∑ k : ZMod N, normSq (∑ j : ZMod N, x j * chi N (j * k))
      = N * ∑ j : ZMod N, normSq (x j) := by
  have key : ∀ k : ZMod N,
      ((normSq (∑ j : ZMod N, x j * chi N (j * k)) : ℝ) : ℂ)
        = ∑ j : ZMod N, ∑ l : ZMod N, (x j * conj (x l)) * chi N ((j - l) * k) := by
    intro k
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, chi_conj]
    have h : chi N (j * k) * chi N (-(l * k)) = chi N ((j - l) * k) := by
      rw [← chi_add]; congr 1; ring
    calc x j * chi N (j * k) * (conj (x l) * chi N (-(l * k)))
        = (x j * conj (x l)) * (chi N (j * k) * chi N (-(l * k))) := by ring
      _ = _ := by rw [h]
  have main : ((∑ k : ZMod N, normSq (∑ j : ZMod N, x j * chi N (j * k)) : ℝ) : ℂ)
      = ((N * ∑ j : ZMod N, normSq (x j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [key]
    have h3 : ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N, (x j * conj (x l)) * chi N ((j - l) * k)
        = ∑ j : ZMod N, ∑ l : ZMod N, ∑ k : ZMod N,
            (x j * conj (x l)) * chi N ((j - l) * k) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm ..
    rw [h3]
    have h2 : ∀ j l : ZMod N, ∑ k : ZMod N, (x j * conj (x l)) * chi N ((j - l) * k)
        = (x j * conj (x l)) * (if j - l = 0 then (N : ℂ) else 0) := by
      intro j l; rw [← Finset.mul_sum, sum_chi]
    simp only [h2, sub_eq_zero]
    simp [Finset.sum_ite_eq, Complex.mul_conj, Finset.mul_sum, mul_comm]
  exact_mod_cast main

/-- The Fourier transform turns the backward shift into multiplication by `chi (-k)`. -/
lemma sum_shift_chi [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ∑ j : ZMod N, f (j + 1) * chi N (j * k)
      = chi N (-k) * ∑ j : ZMod N, f j * chi N (j * k) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun j => ?_)
  simp only [Equiv.coe_addRight]
  rw [show chi N (-k) * (f (j + 1) * chi N ((j + 1) * k))
      = f (j + 1) * (chi N (-k) * chi N ((j + 1) * k)) by ring, ← chi_add]
  congr 2
  ring

end Character

/-! ## An elementary bound on cosines -/

lemma cos_two_pi_mul_le (N v : ℕ) (h1 : 1 ≤ v) (h2 : v < N) :
    Real.cos (2 * Real.pi * v / N) ≤ Real.cos (2 * Real.pi / N) := by
  have hN0 : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  have hpi := Real.pi_pos
  set w := min v (N - v) with hw
  have hw1 : 1 ≤ w := by simp [hw]; omega
  have hw2 : 2 * w ≤ N := by simp [hw]; omega
  have hcos : Real.cos (2 * Real.pi * v / N) = Real.cos (2 * Real.pi * w / N) := by
    rcases le_total v (N - v) with h | h
    · rw [hw, min_eq_left h]
    · rw [hw, min_eq_right h]
      have h3 : (2 * Real.pi * ((N - v : ℕ) : ℝ) / N) = 2 * Real.pi - 2 * Real.pi * v / N := by
        have h4 : ((N - v : ℕ) : ℝ) = (N : ℝ) - v := by
          have hle : v ≤ N := le_of_lt h2
          push_cast [hle]; ring
        rw [h4]; field_simp
      rw [h3, Real.cos_two_pi_sub]
  rw [hcos]
  have hw1' : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
  · rw [div_le_iff₀ hN]
    have : (2 : ℝ) * w ≤ N := by exact_mod_cast hw2
    nlinarith
  · rw [div_le_div_iff_of_pos_right hN]
    nlinarith

/-! ## The Laplacian of the cycle graph -/

section Cycle

variable {m : ℕ}

lemma sum_shift_add {α : Type*} [AddCommMonoid α] (f : ZMod (m + 3) → α) :
    ∑ i : ZMod (m + 3), f (i + 1) = ∑ i : ZMod (m + 3), f i :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod (m + 3))) _ _ (fun _ => rfl)

lemma sum_shift_sub {α : Type*} [AddCommMonoid α] (f : ZMod (m + 3) → α) :
    ∑ i : ZMod (m + 3), f (i - 1) = ∑ i : ZMod (m + 3), f i :=
  Fintype.sum_equiv (Equiv.subRight (1 : ZMod (m + 3))) _ _ (fun _ => rfl)

lemma one_ne_zero_zmod : (1 : ZMod (m + 3)) ≠ 0 := by
  have hv : ((1 : ℕ) : ZMod (m + 3)).val = 1 := ZMod.val_cast_of_lt (by omega)
  intro hc
  rw [show ((1 : ℕ) : ZMod (m + 3)) = (1 : ZMod (m + 3)) by push_cast; ring, hc] at hv
  simp at hv

lemma val_one_zmod : (1 : ZMod (m + 3)).val = 1 := by
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by push_cast; ring]
  exact ZMod.val_cast_of_lt (by omega)

lemma two_ne_zero_zmod : (2 : ZMod (m + 3)) ≠ 0 := by
  have hv : ((2 : ℕ) : ZMod (m + 3)).val = 2 := ZMod.val_cast_of_lt (by omega)
  intro hc
  rw [show ((2 : ℕ) : ZMod (m + 3)) = (2 : ZMod (m + 3)) by push_cast; ring, hc] at hv
  simp at hv

lemma lap_mulVec (x : ZMod (m + 3) → ℝ) (i : ZMod (m + 3)) :
    ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i = 2 * x i - x (i - 1) - x (i + 1) := by
  have hne : (i - 1 : ZMod (m + 3)) ≠ i + 1 := fun h =>
    two_ne_zero_zmod (by linear_combination -h)
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  have hdeg : (cycleGraph (m + 3)).degree i = 2 := cycleGraph_degree_three_le
  have hnb : (cycleGraph (m + 3)).neighborFinset i = {i - 1, i + 1} := cycleGraph_neighborFinset
  have hs : ∑ u ∈ ({i - 1, i + 1} : Finset (Fin (m + 3))), x u = x (i - 1) + x (i + 1) :=
    Finset.sum_pair hne
  rw [hdeg, hnb, hs]
  push_cast
  ring

lemma lap_quadForm (x : ZMod (m + 3) → ℝ) :
    x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
      = ∑ i : ZMod (m + 3), (x i - x (i + 1)) ^ 2 := by
  have h1 : x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
      = ∑ i : ZMod (m + 3), x i * (2 * x i - x (i - 1) - x (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [lap_mulVec]
  have h2 : ∑ i : ZMod (m + 3), x i * x (i - 1) = ∑ i : ZMod (m + 3), x i * x (i + 1) := by
    refine (Fintype.sum_equiv (Equiv.addRight (1 : ZMod (m + 3)))
      (fun i => x i * x (i + 1)) (fun i => x i * x (i - 1)) (fun i => ?_)).symm
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    exact mul_comm _ _
  have h3 : ∑ i : ZMod (m + 3), (x (i + 1)) ^ 2 = ∑ i : ZMod (m + 3), (x i) ^ 2 :=
    sum_shift_add (fun i => (x i) ^ 2)
  have e1 : ∑ i : ZMod (m + 3), x i * (2 * x i - x (i - 1) - x (i + 1))
      = 2 * (∑ i : ZMod (m + 3), (x i) ^ 2) - (∑ i : ZMod (m + 3), x i * x (i - 1))
        - ∑ i : ZMod (m + 3), x i * x (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i : ZMod (m + 3), (x i - x (i + 1)) ^ 2
      = (∑ i : ZMod (m + 3), (x i) ^ 2) + (∑ i : ZMod (m + 3), (x (i + 1)) ^ 2)
        - 2 * ∑ i : ZMod (m + 3), x i * x (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, e1, e2, h3, h2]
  ring

/-- The key spectral estimate: on the hyperplane `∑ x = 0`, the Laplacian quadratic form of
the cycle is bounded below by the Fiedler value times the squared norm. -/
lemma cycle_quad_lower (x : ZMod (m + 3) → ℝ) (hsum : ∑ j : ZMod (m + 3), x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) * (∑ j : ZMod (m + 3), (x j) ^ 2)
      ≤ ∑ j : ZMod (m + 3), (x j - x (j + 1)) ^ 2 := by
  have hNpos : (0 : ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  -- the discrete Fourier coefficients of `x`
  have h1 : ∑ k : ZMod (m + 3), normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k))
      = ((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j) ^ 2 := by
    have h := parseval (N := m + 3) (fun j => ((x j : ℝ) : ℂ))
    simpa [Complex.normSq_ofReal, sq] using h
  have hX0 : (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * 0)) = 0 := by
    simp only [mul_zero, chi_zero, mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_zero]
  have h3 : normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * 0)) = 0 := by
    rw [hX0, map_zero]
  have hterm : ∀ k : ZMod (m + 3),
      normSq (∑ j : ZMod (m + 3), ((x j - x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k))
        = (2 - 2 * (chi (m + 3) k).re) *
            normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)) := by
    intro k
    have hsplit : ∑ j : ZMod (m + 3), ((x j - x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k)
        = (1 - chi (m + 3) (-k)) * ∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k) := by
      have hpt : ∀ j : ZMod (m + 3), ((x j - x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k)
          = ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)
            - ((x (j + 1) : ℝ) : ℂ) * chi (m + 3) (j * k) := by
        intro j; push_cast; ring
      rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib,
        sum_shift_chi (fun j => ((x j : ℝ) : ℂ)) k]
      ring
    have hre : (chi (m + 3) (-k)).re = (chi (m + 3) k).re := by rw [← chi_conj]; simp
    have hn1 : normSq (1 - chi (m + 3) (-k)) = 2 - 2 * (chi (m + 3) k).re := by
      have hns := chi_normSq (N := m + 3) (-k)
      rw [Complex.normSq_apply] at hns
      rw [hre] at hns
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hre]
      linear_combination hns
    rw [hsplit, Complex.normSq_mul, hn1]
  have h2 : ∑ k : ZMod (m + 3), (2 - 2 * (chi (m + 3) k).re) *
        normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k))
      = ((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j - x (j + 1)) ^ 2 := by
    have h := parseval (N := m + 3) (fun j => ((x j - x (j + 1) : ℝ) : ℂ))
    rw [Finset.sum_congr rfl (fun k _ => (hterm k).symm)]
    simpa [← Complex.ofReal_sub, Complex.normSq_ofReal, sq] using h
  have h4 : ∀ k : ZMod (m + 3),
      (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
          normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k))
        ≤ (2 - 2 * (chi (m + 3) k).re) *
          normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [h3]; ring_nf; rfl
    · have hAk : 0 ≤ normSq (∑ j : ZMod (m + 3), ((x j : ℝ) : ℂ) * chi (m + 3) (j * k)) :=
        normSq_nonneg _
      have hcos : (chi (m + 3) k).re ≤ Real.cos (2 * Real.pi / (m + 3)) := by
        rw [chi_re]
        have hv1 : 1 ≤ k.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk)
        have hb := cos_two_pi_mul_le (m + 3) k.val hv1 k.val_lt
        push_cast at hb ⊢
        exact hb
      nlinarith
  have hchain : (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
      (((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j) ^ 2)
      ≤ ((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j - x (j + 1)) ^ 2 := by
    rw [← h1, ← h2, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => h4 k)
  rw [show (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
      (((m + 3 : ℕ) : ℝ) * ∑ j : ZMod (m + 3), (x j) ^ 2)
      = ((m + 3 : ℕ) : ℝ) * ((2 - 2 * Real.cos (2 * Real.pi / (m + 3))) *
        ∑ j : ZMod (m + 3), (x j) ^ 2) from by ring] at hchain
  exact le_of_mul_le_mul_left hchain hNpos

/-- The eigenvector realizing the Fiedler value. -/
noncomputable def fiedlerVec (m : ℕ) : ZMod (m + 3) → ℝ := fun j => (chi (m + 3) j).re

lemma fiedlerVec_zero : fiedlerVec m 0 = 1 := by simp [fiedlerVec, chi_zero]

lemma fiedlerVec_sum : ∑ j : ZMod (m + 3), fiedlerVec m j = 0 := by
  have h1 : ∑ j : ZMod (m + 3), chi (m + 3) j = 0 := by
    have h := sum_chi (N := m + 3) 1
    simp only [one_mul, if_neg one_ne_zero_zmod] at h
    exact h
  have h2 : ∑ j : ZMod (m + 3), fiedlerVec m j = (∑ j : ZMod (m + 3), chi (m + 3) j).re := by
    simp [fiedlerVec, Complex.re_sum]
  rw [h2, h1, Complex.zero_re]

lemma fiedlerVec_eigen (i : ZMod (m + 3)) :
    2 * fiedlerVec m i - fiedlerVec m (i - 1) - fiedlerVec m (i + 1)
      = (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) * fiedlerVec m i := by
  have hc1 : (chi (m + 3) 1).re = Real.cos (2 * Real.pi / (m + 3)) := by
    rw [chi_re, val_one_zmod]
    norm_num
  have hsum : chi (m + 3) (i - 1) + chi (m + 3) (i + 1)
      = chi (m + 3) i * ((2 * (chi (m + 3) 1).re : ℝ) : ℂ) := by
    have e1 : chi (m + 3) (i - 1) = chi (m + 3) i * chi (m + 3) (-1) := by
      rw [← chi_add]; congr 1; ring
    have e2 : chi (m + 3) (i + 1) = chi (m + 3) i * chi (m + 3) 1 := chi_add i 1
    rw [e1, e2, ← chi_conj, ← mul_add, add_comm (conj _) _]
    congr 1
    exact Complex.add_conj _
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hre
  simp only [fiedlerVec]
  rw [← hc1]
  linarith [hre]

lemma fiedler_pos : 0 < 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3)) := by
  have hpi := Real.pi_pos
  have h1 : 0 < 2 * Real.pi / ((m : ℝ) + 3) := by positivity
  have h2 : 2 * Real.pi / ((m : ℝ) + 3) < Real.pi := by
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have := (Real.mapsTo_cos_Ioo (Set.mem_Ioo.mpr ⟨h1, h2⟩)).2
  linarith

lemma fiedlerVec_ne_zero : fiedlerVec m ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : ZMod (m + 3))
  rw [fiedlerVec_zero] at h0
  exact one_ne_zero h0

lemma fiedlerVec_lap : (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fiedlerVec m
    = (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))) • fiedlerVec m := by
  funext i
  rw [lap_mulVec]
  exact fiedlerVec_eigen i

lemma sum_sq_pos {x : ZMod (m + 3) → ℝ} (hx : x ≠ 0) : 0 < ∑ i : ZMod (m + 3), (x i) ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hle : (x i) ^ 2 ≤ ∑ j : ZMod (m + 3), (x j) ^ 2 :=
    Finset.single_le_sum (f := fun j : ZMod (m + 3) => (x j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have : 0 < (x i) ^ 2 := pow_two_pos_of_ne_zero hi
  linarith

/-- The Fiedler value of the cycle, stated for the index type `ZMod (m+3)`. -/
lemma cycle_fiedler_value_aux (m : ℕ) :
    IsLeast {r : ℝ | ∃ x : ZMod (m + 3) → ℝ, x ≠ 0 ∧ (∑ i : ZMod (m + 3), x i = 0) ∧
        r = (x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)) / (∑ i : ZMod (m + 3), x i ^ 2)}
      (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))) ∧
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : ZMod (m + 3) → ℝ, v ≠ 0 ∧
        (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))) := by
  set mu : ℝ := 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))
  have hmupos : 0 < mu := fiedler_pos
  have hv2 : 0 < ∑ i : ZMod (m + 3), (fiedlerVec m i) ^ 2 := sum_sq_pos fiedlerVec_ne_zero
  have hlower : ∀ x : ZMod (m + 3) → ℝ, (∑ i : ZMod (m + 3), x i = 0) →
      mu * (∑ i : ZMod (m + 3), (x i) ^ 2) ≤ x ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) := by
    intro x hsum
    rw [lap_quadForm]
    exact cycle_quad_lower x hsum
  have hQv : fiedlerVec m ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ fiedlerVec m)
      = mu * ∑ i : ZMod (m + 3), (fiedlerVec m i) ^ 2 := by
    rw [fiedlerVec_lap, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
  constructor
  · constructor
    · refine ⟨fiedlerVec m, fiedlerVec_ne_zero, fiedlerVec_sum, ?_⟩
      rw [hQv, mul_div_assoc, div_self (ne_of_gt hv2), mul_one]
    · rintro r ⟨x, hx, hxsum, rfl⟩
      have hx2 : 0 < ∑ i : ZMod (m + 3), (x i) ^ 2 := sum_sq_pos hx
      rw [le_div_iff₀ hx2]
      exact hlower x hxsum
  · constructor
    · exact ⟨ne_of_gt hmupos, fiedlerVec m, fiedlerVec_ne_zero, fiedlerVec_lap⟩
    · rintro nu ⟨hnu0, v, hv, hlap⟩
      have hvsum : ∑ i : ZMod (m + 3), v i = 0 := by
        have hz : ∑ i : ZMod (m + 3), ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v) i = 0 := by
          have hpt : ∀ i : ZMod (m + 3), ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v) i
              = 2 * v i - v (i - 1) - v (i + 1) := fun i => lap_mulVec v i
          rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib,
            Finset.sum_sub_distrib, sum_shift_sub (fun i => v i), sum_shift_add (fun i => v i),
            ← Finset.mul_sum]
          ring
        rw [hlap] at hz
        have hz2 : nu * ∑ i : ZMod (m + 3), v i = 0 := by
          rw [← hz, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]
        exact (mul_eq_zero.mp hz2).resolve_left hnu0
      have hv2' : 0 < ∑ i : ZMod (m + 3), (v i) ^ 2 := sum_sq_pos hv
      have hQ : v ⬝ᵥ ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ v)
          = nu * ∑ i : ZMod (m + 3), (v i) ^ 2 := by
        rw [hlap, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
      have hkey := hlower v hvsum
      rw [hQ] at hkey
      exact le_of_mul_le_mul_right (by linarith) hv2'

end Cycle

/-- **The Fiedler value (algebraic connectivity) of the cycle graph `C n`,
for `n ≥ 3`, equals `2 - 2 cos (2π/n)`.**

Two equivalent formulations are given:
* it is the minimum of the Rayleigh quotient of the Laplacian over nonzero vectors orthogonal
  to the all-ones vector (the variational characterization of the second smallest Laplacian
  eigenvalue);
* it is the smallest nonzero eigenvalue of the Laplacian matrix of `C n`. -/
theorem cycle_fiedler_value {n : ℕ} (hn : 3 ≤ n) :
    IsLeast {r : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (∑ i, x i = 0) ∧
        r = (x ⬝ᵥ ((cycleGraph n).lapMatrix ℝ *ᵥ x)) / (∑ i, x i ^ 2)}
      (2 - 2 * Real.cos (2 * Real.pi / n)) ∧
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧
        (cycleGraph n).lapMatrix ℝ *ᵥ v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hcast : ((m + 3 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
  rw [hcast]
  exact cycle_fiedler_value_aux m

/-- Sanity check: the Fiedler value of the triangle `C 3` is `3`. -/
theorem cycle_fiedler_value_three :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : Fin 3 → ℝ, v ≠ 0 ∧
      (cycleGraph 3).lapMatrix ℝ *ᵥ v = μ • v} 3 := by
  have h := (cycle_fiedler_value (n := 3) le_rfl).2
  have hval : (2 : ℝ) - 2 * Real.cos (2 * Real.pi / ((3 : ℕ) : ℝ)) = 3 := by
    rw [show (2 * Real.pi / ((3 : ℕ) : ℝ)) = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  rwa [hval] at h

end Frontier.Spectral

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

