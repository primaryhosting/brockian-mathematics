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
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/
lemma cycleGraph_adj_iff (hm : 2 ≤ m) (u v : Fin (m + 1)) :
    (cycleGraph (m + 1)).Adj u v ↔ (v = u + 1 ∨ u = v + 1) := by
  have h1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ a b : Fin (m + 1), (a - b).val = 1 ↔ a = b + 1 := by
    intro a b
    have e : ((a - b).val = ((1 : Fin (m + 1)).val)) ↔ (a - b = 1) := Fin.val_inj
    rw [h1] at e
    rw [e, sub_eq_iff_eq_add, add_comm (1 : Fin (m + 1)) b]
  rw [SimpleGraph.cycleGraph_adj', key, key]
  tauto

/-- In `Fin (m+1)` with `m ≥ 2`, the two cyclic neighbours of a vertex are distinct. -/
lemma succ_ne_pred (hm : 2 ≤ m) (i : Fin (m + 1)) : i + 1 ≠ i - 1 := by
  have h1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  intro h
  have h2 : (1 : Fin (m + 1)) + 1 = 0 := by
    have hc : i + ((1 : Fin (m + 1)) + 1) = i + 0 := by
      rw [← add_assoc, h, add_zero, sub_add_cancel]
    exact add_left_cancel hc
  have h3 := congrArg Fin.val h2
  rw [Fin.val_add, h1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h3
  omega

/-- Summing a function against the adjacency relation of the cycle graph. -/
lemma cycle_sum_adj (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j, (if (cycleGraph (m + 1)).Adj i j then x j else 0) = x (i + 1) + x (i - 1) := by
  have hne : i + 1 ≠ i - 1 := succ_ne_pred hm i
  have hsplit : ∀ j : Fin (m + 1), (if (cycleGraph (m + 1)).Adj i j then x j else 0)
      = (if j = i + 1 then x j else 0) + (if j = i - 1 then x j else 0) := by
    intro j
    have hiff := cycleGraph_adj_iff hm i j
    have hj : (i = j + 1) ↔ (j = i - 1) := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    by_cases h1 : j = i + 1
    · have hA : (cycleGraph (m + 1)).Adj i j := hiff.mpr (Or.inl h1)
      have h2 : j ≠ i - 1 := by rw [h1]; exact hne
      rw [if_pos hA, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : j = i - 1
      · have hA : (cycleGraph (m + 1)).Adj i j := hiff.mpr (Or.inr (hj.mpr h2))
        rw [if_pos hA, if_neg h1, if_pos h2, zero_add]
      · have hA : ¬ (cycleGraph (m + 1)).Adj i j := by
          intro hA
          rcases hiff.mp hA with h | h
          · exact h1 h
          · exact h2 (hj.mp h)
        rw [if_neg hA, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simp

/-- The degree of every vertex of the cycle graph `C_{m+1}` (`m ≥ 2`) is `2`. -/
lemma cycle_degree (hm : 2 ≤ m) (i : Fin (m + 1)) : (cycleGraph (m + 1)).degree i = 2 := by
  have h := cycle_sum_adj hm (fun _ => (1 : ℝ)) i
  rw [← Finset.sum_filter] at h
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.trans (by norm_num : (1 : ℝ) + 1 = 2)

/-- The Laplacian of the cycle graph acts as the discrete second difference. -/
lemma cycle_lap_mulVec (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ((cycleGraph (m + 1)).lapMatrix ℝ *ᵥ x) i = 2 * x i - x (i + 1) - x (i - 1) := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply,
    SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_filter, cycle_sum_adj hm]
  have hdeg : (SimpleGraph.degMatrix ℝ (cycleGraph (m + 1)) *ᵥ x) i = 2 * x i := by
    simp [SimpleGraph.degMatrix, Matrix.mulVec, Matrix.diagonal, dotProduct, cycle_degree hm]
  rw [hdeg]
  ring

end Combinatorics

section Fourier

/-- The standard primitive `n`-th root of unity. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

variable {n : ℕ}

lemma isPrimitiveRoot_zeta (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma zeta_pow_self (hn : n ≠ 0) : zeta n ^ n = 1 := (isPrimitiveRoot_zeta hn).pow_eq_one

lemma zeta_ne_zero : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_mod (hn : n ≠ 0) (a : ℕ) : zeta n ^ a = zeta n ^ (a % n) := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, zeta_pow_self hn, one_pow, one_mul]

lemma zeta_pow_congr (hn : n ≠ 0) {a b : ℕ} (h : a % n = b % n) : zeta n ^ a = zeta n ^ b := by
  rw [zeta_pow_mod hn a, zeta_pow_mod hn b, h]

lemma zeta_pow_eq_exp (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast
  field_simp

lemma re_zeta_pow (hn : n ≠ 0) (k : ℕ) :
    (zeta n ^ k).re = Real.cos (2 * Real.pi * k / n) := by
  rw [zeta_pow_eq_exp hn k, Complex.exp_ofReal_mul_I_re]

lemma im_zeta_pow (hn : n ≠ 0) (k : ℕ) :
    (zeta n ^ k).im = Real.sin (2 * Real.pi * k / n) := by
  rw [zeta_pow_eq_exp hn k, Complex.exp_ofReal_mul_I_im]

lemma normSq_zeta_pow (hn : n ≠ 0) (k : ℕ) : Complex.normSq (zeta n ^ k) = 1 := by
  rw [Complex.normSq_apply, re_zeta_pow hn, im_zeta_pow hn]
  have := Real.sin_sq_add_cos_sq (2 * Real.pi * k / n)
  nlinarith [this]

lemma normSq_one_sub_zeta_pow (hn : n ≠ 0) (k : ℕ) :
    Complex.normSq (1 - zeta n ^ k) = 2 - 2 * Real.cos (2 * Real.pi * k / n) := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    re_zeta_pow hn, im_zeta_pow hn]
  have := Real.sin_sq_add_cos_sq (2 * Real.pi * k / n)
  nlinarith [this]

lemma conj_zeta_pow (hn : n ≠ 0) (s : ℕ) :
    (starRingEnd ℂ) (zeta n ^ s) = zeta n ^ ((n - 1) * s) := by
  have hns : Complex.normSq (zeta n) = 1 := by simpa using normSq_zeta_pow (k := 1) hn
  have h1 : zeta n * (starRingEnd ℂ) (zeta n) = 1 := by
    rw [Complex.mul_conj, hns]
    norm_num
  have h2 : zeta n * zeta n ^ (n - 1) = 1 := by
    rw [← pow_succ']
    have hnn : (n - 1) + 1 = n := by omega
    rw [hnn, zeta_pow_self hn]
  have hbase : (starRingEnd ℂ) (zeta n) = zeta n ^ (n - 1) :=
    mul_left_cancel₀ zeta_ne_zero (h1.trans h2.symm)
  rw [map_pow, hbase, ← pow_mul]

lemma zeta_geom_sum (hn : n ≠ 0) (t : ℕ) :
    ∑ k ∈ Finset.range n, (zeta n ^ t) ^ k = if n ∣ t then (n : ℂ) else 0 := by
  by_cases h : n ∣ t
  · rw [if_pos h]
    have h1 : zeta n ^ t = 1 := ((isPrimitiveRoot_zeta hn).pow_eq_one_iff_dvd t).mpr h
    simp [h1]
  · rw [if_neg h]
    have hne : zeta n ^ t ≠ 1 := fun hh => h (((isPrimitiveRoot_zeta hn).pow_eq_one_iff_dvd t).mp hh)
    rw [geom_sum_eq hne]
    have hpow : (zeta n ^ t) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_self hn, one_pow]
    rw [hpow]
    simp

lemma dvd_shift_iff (hn : n ≠ 0) (j l : Fin n) :
    n ∣ (j.val + (n - 1) * l.val) ↔ j = l := by
  constructor
  · intro hdvd
    have hone : (1:ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hz : (n : ℤ) ∣ ((j.val : ℤ) - (l.val : ℤ)) := by
      obtain ⟨c, hc⟩ := hdvd
      have hcz : (j.val : ℤ) + ((n : ℤ) - 1) * (l.val : ℤ) = (n : ℤ) * c := by
        have hh := congrArg (fun t : ℕ => (t : ℤ)) hc
        push_cast [Nat.cast_sub hone] at hh
        linarith [hh]
      exact ⟨c - l.val, by linarith [hcz]⟩
    have hlt : |((j.val : ℤ) - (l.val : ℤ))| < (n : ℤ) := by
      have h1 := j.isLt
      have h2 := l.isLt
      rw [abs_lt]
      omega
    have := Int.eq_zero_of_abs_lt_dvd hz hlt
    have : (j.val : ℤ) = (l.val : ℤ) := by linarith
    exact Fin.val_inj.mp (by exact_mod_cast this)
  · rintro rfl
    refine ⟨j.val, ?_⟩
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    cases n with
    | zero => omega
    | succ p => simp; ring

lemma zeta_orthogonality (hn : n ≠ 0) (j l : Fin n) :
    ∑ k ∈ Finset.range n, zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k))
      = if j = l then (n : ℂ) else 0 := by
  have hterm : ∀ k, zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k))
      = (zeta n ^ (j.val + (n - 1) * l.val)) ^ k := by
    intro k
    rw [conj_zeta_pow hn, ← pow_add, ← pow_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), zeta_geom_sum hn]
  simp only [dvd_shift_iff hn]

/-- Discrete Fourier transform of a real vector indexed by `Fin n`. -/
noncomputable def dft (n : ℕ) (x : Fin n → ℝ) (k : ℕ) : ℂ :=
  ∑ j : Fin n, (x j : ℂ) * zeta n ^ (j.val * k)

lemma dft_zero (x : Fin n → ℝ) : dft n x 0 = ((∑ j, x j : ℝ) : ℂ) := by
  simp [dft]

/-- Parseval's identity for the discrete Fourier transform. -/
lemma parseval (hn : n ≠ 0) (x : Fin n → ℝ) :
    ∑ k ∈ Finset.range n, Complex.normSq (dft n x k) = n * ∑ j, (x j) ^ 2 := by
  have key : ∑ k ∈ Finset.range n, ((Complex.normSq (dft n x k) : ℝ) : ℂ)
      = ((n : ℂ)) * ∑ j, ((x j : ℂ)) ^ 2 := by
    have step1 : ∀ k, ((Complex.normSq (dft n x k) : ℝ) : ℂ)
        = ∑ j : Fin n, ∑ l : Fin n, ((x j : ℂ) * (x l : ℂ)) *
          (zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k))) := by
      intro k
      rw [← Complex.mul_conj, dft, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      ring
    rw [Finset.sum_congr rfl (fun k _ => step1 k), Finset.sum_comm]
    have step2 : ∀ j : Fin n, ∑ k ∈ Finset.range n, ∑ l : Fin n,
        ((x j : ℂ) * (x l : ℂ)) * (zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k)))
        = ((x j : ℂ)) ^ 2 * n := by
      intro j
      rw [Finset.sum_comm]
      have : ∀ l : Fin n, ∑ k ∈ Finset.range n,
          ((x j : ℂ) * (x l : ℂ)) * (zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k)))
          = ((x j : ℂ) * (x l : ℂ)) * (if j = l then (n : ℂ) else 0) := by
        intro l
        rw [← Finset.mul_sum, zeta_orthogonality hn]
      rw [Finset.sum_congr rfl (fun l _ => this l)]
      simp [sq]
    rw [Finset.sum_congr rfl (fun j _ => step2 j), ← Finset.sum_mul, mul_comm]
  have hcast : ((∑ k ∈ Finset.range n, Complex.normSq (dft n x k) : ℝ) : ℂ)
      = ((n * ∑ j, (x j) ^ 2 : ℝ) : ℂ) := by
    push_cast at key ⊢
    exact key
  exact_mod_cast hcast

end Fourier

section Dirichlet

variable {m : ℕ}

private lemma val_one (hm : 2 ≤ m) : ((1 : Fin (m + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)

/-- The Fourier transform turns the cyclic shift into multiplication by `ζ ^ k`. -/
lemma dft_shift (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (k : ℕ) :
    dft (m + 1) (fun j => x (j - 1)) k = zeta (m + 1) ^ k * dft (m + 1) x k := by
  have hone := val_one hm
  have key : ∀ i : Fin (m + 1),
      ((x ((i + 1) - 1) : ℂ) * zeta (m + 1) ^ ((i + 1).val * k))
        = zeta (m + 1) ^ k * ((x i : ℂ) * zeta (m + 1) ^ (i.val * k)) := by
    intro i
    have h1 : (i + 1) - 1 = i := by simp
    have hval : ((i + 1).val * k) % (m + 1) = ((i.val * k) + k) % (m + 1) := by
      rw [Fin.val_add, hone, Nat.mod_mul_mod]
      congr 1
      ring
    rw [h1, zeta_pow_congr (n := m + 1) (by omega) hval, pow_add]
    ring
  calc dft (m + 1) (fun j => x (j - 1)) k
      = ∑ i : Fin (m + 1), ((x ((i + 1) - 1) : ℂ) * zeta (m + 1) ^ ((i + 1).val * k)) :=
        (Fintype.sum_equiv (Equiv.addRight (1 : Fin (m + 1))) _ _ (fun _ => rfl)).symm
    _ = ∑ i : Fin (m + 1), zeta (m + 1) ^ k * ((x i : ℂ) * zeta (m + 1) ^ (i.val * k)) :=
        Finset.sum_congr rfl (fun i _ => key i)
    _ = zeta (m + 1) ^ k * dft (m + 1) x k := by rw [dft, Finset.mul_sum]

/-- The Fourier transform of the cyclic difference. -/
lemma dft_diff (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (k : ℕ) :
    dft (m + 1) (fun j => x j - x (j - 1)) k = (1 - zeta (m + 1) ^ k) * dft (m + 1) x k := by
  have hsub : dft (m + 1) (fun j => x j - x (j - 1)) k
      = dft (m + 1) x k - dft (m + 1) (fun j => x (j - 1)) k := by
    simp only [dft, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hsub, dft_shift hm]
  ring

/-- On the cycle `C_{m+1}`, the frequency-`k` eigenvalue is minimised (over `k ≠ 0`) at `k = 1`. -/
lemma cos_arg_le (hm : 2 ≤ m) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m) :
    Real.cos (2 * Real.pi * k / ((m : ℝ) + 1)) ≤ Real.cos (2 * Real.pi / ((m : ℝ) + 1)) := by
  have hpi := Real.pi_pos
  have hN : (3 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hNpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk2
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hA0 : 0 ≤ 2 * Real.pi / N := by positivity
  have hApi : 2 * Real.pi / N ≤ Real.pi := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hAT : 2 * Real.pi / N ≤ 2 * Real.pi * k / N := by
    apply div_le_div_of_nonneg_right ?_ hNpos.le
    nlinarith
  have hT2 : 2 * Real.pi * k / N ≤ 2 * Real.pi - 2 * Real.pi / N := by
    rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hNpos]
    nlinarith
  by_cases hTpi : 2 * Real.pi * k / N ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hA0 hTpi hAT
  · push_neg at hTpi
    have h1 : 2 * Real.pi - 2 * Real.pi * k / N ≤ Real.pi := by linarith
    have h2 : 2 * Real.pi / N ≤ 2 * Real.pi - 2 * Real.pi * k / N := by linarith
    have h3 := Real.cos_le_cos_of_nonneg_of_le_pi hA0 h1 h2
    rwa [Real.cos_two_pi_sub] at h3

/-- **Discrete Poincaré / Wirtinger inequality on the cycle.**  For a mean-zero vector on the
cycle `C_{m+1}`, the Dirichlet energy is at least `2 - 2 cos (2π/(m+1))` times the squared norm. -/
lemma dirichlet_lower (hm : 2 ≤ m) (x : Fin (m + 1) → ℝ) (hsum : ∑ j, x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 1))) * (∑ j, (x j) ^ 2)
      ≤ ∑ j, (x j - x (j - 1)) ^ 2 := by
  have hn0 : (m + 1) ≠ 0 := Nat.succ_ne_zero m
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  set L : ℝ := 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 1)) with hL
  have hterm : ∀ k ∈ Finset.range (m + 1),
      L * Complex.normSq (dft (m + 1) x k)
        ≤ Complex.normSq (dft (m + 1) (fun j => x j - x (j - 1)) k) := by
    intro k hk
    rw [dft_diff hm, Complex.normSq_mul, normSq_one_sub_zeta_pow hn0, hc]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hz : dft (m + 1) x 0 = 0 := by rw [dft_zero, hsum]; simp
      rw [hz]
      simp
    · have hk2 : k ≤ m := by
        have := Finset.mem_range.mp hk
        omega
      have hcos := cos_arg_le hm hk1 hk2
      have hnn : 0 ≤ Complex.normSq (dft (m + 1) x k) := Complex.normSq_nonneg _
      nlinarith [hcos, hnn]
  have hsum1 : L * (∑ k ∈ Finset.range (m + 1), Complex.normSq (dft (m + 1) x k))
      ≤ ∑ k ∈ Finset.range (m + 1),
          Complex.normSq (dft (m + 1) (fun j => x j - x (j - 1)) k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  rw [parseval hn0 x, parseval hn0 (fun j => x j - x (j - 1)), hc] at hsum1
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : ((m : ℝ) + 1) * (L * ∑ j, (x j) ^ 2)
      ≤ ((m : ℝ) + 1) * (∑ j, (x j - x (j - 1)) ^ 2) := by
    calc ((m : ℝ) + 1) * (L * ∑ j, (x j) ^ 2)
        = L * (((m : ℝ) + 1) * ∑ j, (x j) ^ 2) := by ring
      _ ≤ ((m : ℝ) + 1) * (∑ j, (x j - x (j - 1)) ^ 2) := hsum1
  exact le_of_mul_le_mul_left h2 hpos

end Dirichlet

end Frontier.Spectral

