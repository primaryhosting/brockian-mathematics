/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma zeta_zpow (n : ℕ) (m : ℤ) :
    zeta n ^ m = Complex.exp (m * (2 * Real.pi * Complex.I / n)) := by
  rw [zeta, ← Complex.exp_int_mul]

lemma zeta_zpow_eq_one_iff {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    zeta n ^ m = 1 ↔ (n : ℤ) ∣ m := by
  rw [zeta_zpow, Complex.exp_eq_one_iff]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : (m : ℂ) = n * k := by field_simp at hk; exact hk
    exact_mod_cast h
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

lemma zeta_zpow_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ} (h : (n : ℤ) ∣ a - b) :
    zeta n ^ a = zeta n ^ b := by
  have h1 : zeta n ^ (a - b) = 1 := (zeta_zpow_eq_one_iff hn _).mpr h
  rw [zpow_sub₀ (zeta_ne_zero n), div_eq_one_iff_eq (zpow_ne_zero _ (zeta_ne_zero n))] at h1
  exact h1

/-- The character sum `∑_{j<n} ζ^{m j}`. -/
lemma zeta_char_sum {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    ∑ j : Fin n, zeta n ^ (m * (j : ℕ)) = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have key : ∀ j : Fin n, zeta n ^ (m * (j : ℕ)) = (zeta n ^ m) ^ (j : ℕ) := by
    intro j; rw [_root_.zpow_mul, zpow_natCast]
  simp_rw [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => (zeta n ^ m) ^ i)]
  by_cases h : (n : ℤ) ∣ m
  · rw [if_pos h, (zeta_zpow_eq_one_iff hn m).mpr h]; simp
  · rw [if_neg h]
    have hne : zeta n ^ m ≠ 1 := fun hc => h ((zeta_zpow_eq_one_iff hn m).mp hc)
    have hpow : (zeta n ^ m) ^ n = 1 := by
      rw [← zpow_natCast (zeta n ^ m) n, ← _root_.zpow_mul]
      exact (zeta_zpow_eq_one_iff hn _).mpr ⟨m, by ring⟩
    rw [geom_sum_eq hne, hpow]; simp

lemma zeta_zpow_add_neg {n : ℕ} (m : ℤ) :
    zeta n ^ m + zeta n ^ (-m) = 2 * (Real.cos (2 * Real.pi * m / n) : ℂ) := by
  have h : ∀ a : ℤ, zeta n ^ a = Complex.exp (((2 * Real.pi * a / n : ℝ) : ℂ) * Complex.I) := by
    intro a
    rw [zeta_zpow]
    congr 1
    push_cast
    ring
  rw [h m, h (-m), Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [show (2 * (Real.pi : ℂ) * (-(m : ℂ)) / n) = -(2 * (Real.pi : ℂ) * (m : ℂ) / n) by ring,
    Complex.cos_neg, Complex.sin_neg]
  ring

/-! ## Elementary facts about `Fin n` arithmetic -/

lemma nat_mod_sub_dvd (n a : ℕ) : (n : ℤ) ∣ ((a % n : ℕ) : ℤ) - (a : ℤ) := by
  refine ⟨-((a / n : ℕ) : ℤ), ?_⟩
  have h : (a : ℤ) = (n : ℤ) * ((a / n : ℕ) : ℤ) + ((a % n : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a n).symm
  rw [h]; ring

lemma fin_shift_dvd {n : ℕ} [NeZero n] (u : Fin n) :
    (n : ℤ) ∣ (((u + 1 : Fin n) : ℕ) : ℤ) - (((u : ℕ) : ℤ) + 1) := by
  have hval : ((u + 1 : Fin n) : ℕ) = ((u : ℕ) + 1) % n := by
    rw [Fin.val_add]
    conv_lhs => rw [Fin.val_one']
    rw [Nat.add_mod ((u : ℕ)) (1 % n) n, Nat.mod_mod_of_dvd, ← Nat.add_mod]
    exact dvd_rfl
  rw [hval]
  have h := nat_mod_sub_dvd n ((u : ℕ) + 1)
  push_cast at h ⊢
  exact h

lemma sub_one_ne_add_one (N : ℕ) (v : Fin (N + 3)) : v - 1 ≠ v + 1 := by
  intro h
  rw [sub_eq_iff_eq_add, add_assoc] at h
  have h0 : (0 : Fin (N + 3)) = 1 + 1 := by simpa using congrArg (fun z => z - v) h
  have h2 : ((0 : Fin (N + 3)) : ℕ) = ((1 + 1 : Fin (N + 3)) : ℕ) := congrArg _ h0
  simp [Fin.val_add, Nat.mod_eq_of_lt] at h2

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian of `C n` acts as the discrete second difference. -/
lemma lap_mulVec (N : ℕ) (x : Fin (N + 3) → ℝ) (v : Fin (N + 3)) :
    ((cycleGraph (N + 3)).lapMatrix ℝ *ᵥ x) v = 2 * x v - x (v - 1) - x (v + 1) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one N v)]
  push_cast
  ring

/-! ## The discrete Fourier transform -/

/-- The `k`-th discrete Fourier coefficient of `y : Fin n → ℂ`. -/
noncomputable def dft (n : ℕ) (y : Fin n → ℂ) (k : ℤ) : ℂ :=
  ∑ j : Fin n, y j * zeta n ^ (-(k * (j : ℕ)))

lemma dft_inversion {n : ℕ} (hn : n ≠ 0) (y : Fin n → ℂ) (i : Fin n) :
    ∑ k : Fin n, dft n y ((k : ℕ) : ℤ) * zeta n ^ (((k : ℕ) : ℤ) * (i : ℕ)) = n * y i := by
  simp only [dft, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hiff : ∀ j : Fin n, ((n : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ↔ j = i := by
    intro j
    constructor
    · intro hdvd
      have h1 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < (n : ℤ) := by
        have := i.isLt; have := j.isLt
        rw [abs_lt]; constructor <;> omega
      have h2 := Int.eq_zero_of_abs_lt_dvd hdvd h1
      exact Fin.ext (by omega)
    · rintro rfl; simp
  have step : ∀ j : Fin n, ∑ k : Fin n,
      y j * zeta n ^ (-(((k : ℕ) : ℤ) * (j : ℕ))) * zeta n ^ (((k : ℕ) : ℤ) * (i : ℕ))
      = y j * (if j = i then (n : ℂ) else 0) := by
    intro j
    rw [← if_congr (hiff j) rfl rfl, ← zeta_char_sum hn (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← zpow_add₀ (zeta_ne_zero n)]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun j _ => step j]
  simp [Finset.sum_ite_eq', mul_comm]

lemma exists_dft_ne_zero {n : ℕ} (hn : n ≠ 0) (y : Fin n → ℂ) (hy : y ≠ 0) :
    ∃ k : Fin n, dft n y ((k : ℕ) : ℤ) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hy
  funext i
  have h := dft_inversion hn y i
  rw [Finset.sum_congr rfl fun k _ => by rw [hcon k, zero_mul]] at h
  simp only [Finset.sum_const_zero] at h
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h0 : (n : ℂ) * y i = 0 := h.symm
  rcases mul_eq_zero.mp h0 with hc | hc
  · exact absurd hc hn'
  · simpa using hc

lemma dft_shift_left {n : ℕ} [NeZero n] (y : Fin n → ℂ) (k : ℤ) :
    ∑ v : Fin n, y (v - 1) * zeta n ^ (-(k * (v : ℕ))) = zeta n ^ (-k) * dft n y k := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [← Fintype.sum_equiv (Equiv.addRight (1 : Fin n))
    (fun u => y (u + 1 - 1) * zeta n ^ (-(k * ((u + 1 : Fin n) : ℕ))))
    (fun v => y (v - 1) * zeta n ^ (-(k * (v : ℕ)))) (fun u => rfl)]
  rw [dft, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [add_sub_cancel_right]
  rw [show zeta n ^ (-(k * (((u + 1 : Fin n) : ℕ) : ℤ)))
      = zeta n ^ (-(k * (((u : ℕ) : ℤ) + 1))) from
    zeta_zpow_congr hn (by
      obtain ⟨c, hc⟩ := fin_shift_dvd u
      exact ⟨-(k * c), by linear_combination (-k) * hc⟩)]
  rw [show (-(k * (((u : ℕ) : ℤ) + 1))) = -k + -(k * ((u : ℕ) : ℤ)) by ring,
    zpow_add₀ (zeta_ne_zero n)]
  ring

lemma dft_shift_right {n : ℕ} [NeZero n] (y : Fin n → ℂ) (k : ℤ) :
    ∑ v : Fin n, y (v + 1) * zeta n ^ (-(k * (v : ℕ))) = zeta n ^ k * dft n y k := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [← Fintype.sum_equiv (Equiv.subRight (1 : Fin n))
    (fun u => y (u - 1 + 1) * zeta n ^ (-(k * ((u - 1 : Fin n) : ℕ))))
    (fun v => y (v + 1) * zeta n ^ (-(k * (v : ℕ)))) (fun u => rfl)]
  rw [dft, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sub_add_cancel]
  rw [show zeta n ^ (-(k * (((u - 1 : Fin n) : ℕ) : ℤ))) = zeta n ^ (k + -(k * ((u : ℕ) : ℤ))) from
    zeta_zpow_congr hn (by
      obtain ⟨c, hc⟩ := fin_shift_dvd (u - 1)
      rw [sub_add_cancel] at hc
      exact ⟨k * c, by linear_combination k * hc⟩)]
  rw [zpow_add₀ (zeta_ne_zero n)]
  ring

/-- If `y` satisfies the eigenvalue equation for the discrete Laplacian, each Fourier
coefficient is either zero or forces `μ` to be the corresponding eigenvalue. -/
lemma dft_eigen {n : ℕ} [NeZero n] (y : Fin n → ℂ) (mu : ℂ) (k : ℤ)
    (hy : ∀ v : Fin n, 2 * y v - y (v - 1) - y (v + 1) = mu * y v) :
    (2 - zeta n ^ k - zeta n ^ (-k)) * dft n y k = mu * dft n y k := by
  have h : ∑ v : Fin n, (2 * y v - y (v - 1) - y (v + 1)) * zeta n ^ (-(k * (v : ℕ)))
      = ∑ v : Fin n, (mu * y v) * zeta n ^ (-(k * (v : ℕ))) :=
    Finset.sum_congr rfl fun v _ => by rw [hy v]
  have e1 : ∑ v : Fin n, (2 * y v - y (v - 1) - y (v + 1)) * zeta n ^ (-(k * (v : ℕ)))
      = 2 * dft n y k - zeta n ^ (-k) * dft n y k - zeta n ^ k * dft n y k := by
    rw [← dft_shift_left y k, ← dft_shift_right y k]
    nth_rewrite 1 [dft]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∑ v : Fin n, (mu * y v) * zeta n ^ (-(k * (v : ℕ))) = mu * dft n y k := by
    rw [dft, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e1, e2] at h
  linear_combination h

/-! ## The eigenvectors -/

/-- The real eigenvector `j ↦ cos (2 π k j / n)` of the cycle Laplacian. -/
noncomputable def cycleVec (n : ℕ) (k : ℤ) (j : Fin n) : ℝ := (zeta n ^ (k * (j : ℕ))).re

lemma cycleVec_zero (n : ℕ) [NeZero n] (k : ℤ) : cycleVec n k 0 = 1 := by
  simp [cycleVec]

lemma cycleVec_ne_zero (n : ℕ) [NeZero n] (k : ℤ) : cycleVec n k ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [cycleVec_zero] at this
  norm_num at this

lemma cycleVec_sum {n : ℕ} (hn : n ≠ 0) {k : ℤ} (hk : ¬ (n : ℤ) ∣ k) :
    ∑ j : Fin n, cycleVec n k j = 0 := by
  have h : ∑ j : Fin n, cycleVec n k j = (∑ j : Fin n, zeta n ^ (k * (j : ℕ))).re := by
    rw [Complex.re_sum]
    rfl
  rw [h, zeta_char_sum hn k, if_neg hk]
  simp

lemma cycleVec_lap (N : ℕ) (k : ℤ) (v : Fin (N + 3)) :
    2 * cycleVec (N + 3) k v - cycleVec (N + 3) k (v - 1) - cycleVec (N + 3) k (v + 1)
      = (2 - 2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ))) * cycleVec (N + 3) k v := by
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  have hL : zeta (N + 3) ^ (k * (((v - 1 : Fin (N + 3)) : ℕ) : ℤ))
        + zeta (N + 3) ^ (k * (((v + 1 : Fin (N + 3)) : ℕ) : ℤ))
      = ((2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ)) : ℝ) : ℂ)
        * zeta (N + 3) ^ (k * ((v : ℕ) : ℤ)) := by
    have h1 : zeta (N + 3) ^ (k * (((v + 1 : Fin (N + 3)) : ℕ) : ℤ))
        = zeta (N + 3) ^ k * zeta (N + 3) ^ (k * ((v : ℕ) : ℤ)) := by
      rw [← zpow_add₀ (zeta_ne_zero _)]
      refine zeta_zpow_congr hn ?_
      obtain ⟨c, hc⟩ := fin_shift_dvd v
      exact ⟨k * c, by linear_combination k * hc⟩
    have h2 : zeta (N + 3) ^ (k * (((v - 1 : Fin (N + 3)) : ℕ) : ℤ))
        = zeta (N + 3) ^ (-k) * zeta (N + 3) ^ (k * ((v : ℕ) : ℤ)) := by
      rw [← zpow_add₀ (zeta_ne_zero _)]
      refine zeta_zpow_congr hn ?_
      obtain ⟨c, hc⟩ := fin_shift_dvd (v - 1)
      rw [sub_add_cancel] at hc
      exact ⟨-(k * c), by linear_combination (-k) * hc⟩
    have h3 := zeta_zpow_add_neg (n := N + 3) k
    have h4 : ((2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ)) : ℝ) : ℂ)
        = zeta (N + 3) ^ k + zeta (N + 3) ^ (-k) := by
      rw [h3]
      push_cast
      ring
    rw [h1, h2, h4]
    ring
  have hre := congrArg Complex.re hL
  rw [Complex.add_re, Complex.re_ofReal_mul] at hre
  simp only [cycleVec]
  linarith

/-! ## Monotonicity of the cosine on the relevant range -/

lemma cos_le_cos_two_pi_div {n k : ℕ} (hn : 3 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    Real.cos (2 * Real.pi * k / n) ≤ Real.cos (2 * Real.pi / n) := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hth_pos : 0 < 2 * Real.pi / n := by positivity
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkn' : (k : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : (k : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hkn
    rw [Nat.cast_sub (by omega)] at h1
    simpa using h1
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlow : 2 * Real.pi / n ≤ 2 * Real.pi * k / n := by
    rw [div_le_div_iff_of_pos_right hnpos]
    nlinarith
  have hhigh : 2 * Real.pi * k / n ≤ 2 * Real.pi - 2 * Real.pi / n := by
    rw [div_le_iff₀ hnpos, sub_mul, div_mul_cancel₀ _ (ne_of_gt hnpos)]
    nlinarith
  rcases le_or_gt (2 * Real.pi * k / n) Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hth_pos.le h hlow
  · rw [show Real.cos (2 * Real.pi * k / n)
        = Real.cos (2 * Real.pi - 2 * Real.pi * k / n) from (Real.cos_two_pi_sub _).symm]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hth_pos.le (by linarith) (by linarith)

lemma cos_two_pi_div_lt_one {n : ℕ} (hn : 3 ≤ n) : Real.cos (2 * Real.pi / n) < 1 := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hth_pos : 0 < 2 * Real.pi / n := by positivity
  have hthpi : 2 * Real.pi / n ≤ Real.pi := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hthpi hth_pos
  simpa using this

/-! ## The spectrum of the cycle Laplacian -/

/-- Every eigenvalue of the cycle Laplacian is of the form `2 - 2 cos (2 π k / n)`, witnessed
by a Fourier mode `k` which is nonzero whenever the eigenvector has vanishing sum. -/
lemma eigenvalue_eq (N : ℕ) (mu : ℝ) (x : Fin (N + 3) → ℝ) (hx : x ≠ 0)
    (hL : (cycleGraph (N + 3)).lapMatrix ℝ *ᵥ x = mu • x) :
    ∃ k : Fin (N + 3), mu = 2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / ((N + 3 : ℕ) : ℝ)) ∧
      ((∑ j, x j) = 0 → (k : ℕ) ≠ 0) := by
  haveI : NeZero (N + 3) := ⟨by omega⟩
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  have hyne : (fun j => ((x j : ℂ))) ≠ (0 : Fin (N + 3) → ℂ) := by
    intro h
    apply hx
    funext i
    have h1 := congrFun h i
    simp only [Pi.zero_apply] at h1
    exact_mod_cast h1
  have hpoint : ∀ v : Fin (N + 3),
      2 * ((x v : ℂ)) - ((x (v - 1) : ℂ)) - ((x (v + 1) : ℂ)) = (mu : ℂ) * ((x v : ℂ)) := by
    intro v
    have h1 := congrFun hL v
    rw [lap_mulVec] at h1
    have h2 : 2 * x v - x (v - 1) - x (v + 1) = mu * x v := by
      simpa [Pi.smul_apply, smul_eq_mul] using h1
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h2
  obtain ⟨k, hk⟩ := exists_dft_ne_zero hn (fun j => ((x j : ℂ))) hyne
  have heq := dft_eigen (fun j => ((x j : ℂ))) (mu : ℂ) ((k : ℕ) : ℤ) hpoint
  have hmu : (2 - zeta (N + 3) ^ ((k : ℕ) : ℤ) - zeta (N + 3) ^ (-((k : ℕ) : ℤ))) = (mu : ℂ) :=
    mul_right_cancel₀ hk heq
  have hcos : (mu : ℂ)
      = ((2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / ((N + 3 : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [← hmu]
    have h3 := zeta_zpow_add_neg (n := N + 3) ((k : ℕ) : ℤ)
    push_cast
    push_cast at h3
    linear_combination -h3
  refine ⟨k, by exact_mod_cast hcos, ?_⟩
  intro hsum h0
  apply hk
  rw [h0]
  simp only [Nat.cast_zero, dft, zero_mul, neg_zero, zpow_zero, mul_one]
  have : ∑ j : Fin (N + 3), ((x j : ℂ)) = ((∑ j : Fin (N + 3), x j : ℝ) : ℂ) := by push_cast; rfl
  rw [this, hsum]
  simp

theorem cycle_lapMatrix_eigenvector (N : ℕ) (k : ℤ) :
    (cycleGraph (N + 3)).lapMatrix ℝ *ᵥ cycleVec (N + 3) k
      = (2 - 2 * Real.cos (2 * Real.pi * k / ((N + 3 : ℕ) : ℝ))) • cycleVec (N + 3) k := by
  funext v
  rw [lap_mulVec, cycleVec_lap]
  rfl

/-! ## Main results -/

/-- The set of Laplacian eigenvalues of the cycle graph `C n` admitting an eigenvector
whose entries sum to zero, i.e. an eigenvector orthogonal to the all-ones vector. -/
def fiedlerSet (n : ℕ) : Set ℝ :=
  {mu : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (∑ j, x j) = 0 ∧
    (cycleGraph n).lapMatrix ℝ *ᵥ x = mu • x}

/-- **The Fiedler value (algebraic connectivity) of the cycle graph `C n` for `n ≥ 3`.**
The smallest Laplacian eigenvalue of `C n` admitting an eigenvector orthogonal to the
all-ones vector (i.e. the second-smallest Laplacian eigenvalue) equals `2 - 2 cos (2 π / n)`. -/
theorem cycle_fiedler_value (n : ℕ) (hn : 3 ≤ n) :
    IsLeast (fiedlerSet n) (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  haveI : NeZero (N + 3) := ⟨by omega⟩
  constructor
  · refine ⟨cycleVec (N + 3) 1, cycleVec_ne_zero _ 1, ?_, ?_⟩
    · refine cycleVec_sum (by omega) ?_
      intro h
      have := Int.le_of_dvd one_pos h
      omega
    · have h := cycle_lapMatrix_eigenvector N 1
      rw [show (2 * Real.pi * ((1 : ℤ) : ℝ) / ((N + 3 : ℕ) : ℝ))
        = 2 * Real.pi / ((N + 3 : ℕ) : ℝ) by push_cast; ring] at h
      exact h
  · rintro mu ⟨x, hx, hsum, hLx⟩
    obtain ⟨k, hmu, hk0⟩ := eigenvalue_eq N mu x hx hLx
    have hkne := hk0 hsum
    have hkle : (k : ℕ) ≤ (N + 3) - 1 := by have := k.isLt; omega
    have hcos := cos_le_cos_two_pi_div (n := N + 3) (k := (k : ℕ)) (by omega) (by omega) hkle
    rw [hmu]
    linarith

/-- The full Laplacian spectrum of the cycle graph `C n`: the eigenvalues are exactly
`2 - 2 cos (2 π k / n)` for `k = 0, …, n-1`. -/
theorem cycle_lapMatrix_spectrum (n : ℕ) (hn : 3 ≤ n) :
    {mu : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (cycleGraph n).lapMatrix ℝ *ᵥ x = mu • x}
      = Set.range (fun k : Fin n => 2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / n)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  haveI : NeZero (N + 3) := ⟨by omega⟩
  ext mu
  constructor
  · rintro ⟨x, hx, hLx⟩
    obtain ⟨k, hmu, -⟩ := eigenvalue_eq N mu x hx hLx
    exact ⟨k, hmu.symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨cycleVec (N + 3) ((k : ℕ) : ℤ), cycleVec_ne_zero _ _, ?_⟩
    have h := cycle_lapMatrix_eigenvector N ((k : ℕ) : ℤ)
    rw [show (2 * Real.pi * (((k : ℕ) : ℤ) : ℝ) / ((N + 3 : ℕ) : ℝ))
      = 2 * Real.pi * ((k : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ) by push_cast; ring] at h
    exact h

/-- The second-smallest Laplacian eigenvalue of `C n`, i.e. the least nonzero eigenvalue,
equals `2 - 2 cos (2 π / n)`. -/
theorem cycle_least_nonzero_eigenvalue (n : ℕ) (hn : 3 ≤ n) :
    IsLeast ({mu : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ (cycleGraph n).lapMatrix ℝ *ᵥ x = mu • x} \ {0})
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  haveI : NeZero (N + 3) := ⟨by omega⟩
  have hpos : 0 < 2 - 2 * Real.cos (2 * Real.pi / ((N + 3 : ℕ) : ℝ)) := by
    have := cos_two_pi_div_lt_one (n := N + 3) (by omega)
    linarith
  constructor
  · refine ⟨⟨cycleVec (N + 3) 1, cycleVec_ne_zero _ 1, ?_⟩, ?_⟩
    · have h := cycle_lapMatrix_eigenvector N 1
      rw [show (2 * Real.pi * ((1 : ℤ) : ℝ) / ((N + 3 : ℕ) : ℝ))
        = 2 * Real.pi / ((N + 3 : ℕ) : ℝ) by push_cast; ring] at h
      exact h
    · simp only [Set.mem_singleton_iff]
      intro h
      rw [h] at hpos
      exact lt_irrefl 0 hpos
  · rintro mu ⟨⟨x, hx, hLx⟩, hmu0⟩
    simp only [Set.mem_singleton_iff] at hmu0
    obtain ⟨k, hmu, -⟩ := eigenvalue_eq N mu x hx hLx
    have hkne : (k : ℕ) ≠ 0 := by
      intro h0
      apply hmu0
      rw [hmu, h0]
      simp
    have hkle : (k : ℕ) ≤ (N + 3) - 1 := by have := k.isLt; omega
    have hcos := cos_le_cos_two_pi_div (n := N + 3) (k := (k : ℕ)) (by omega) (by omega) hkle
    rw [hmu]
    linarith

end Frontier.Spectral

