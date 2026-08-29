/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-! ## Li coefficients of a finite family of zeros -/

/-- The `n`-th **Li coefficient** attached to a finite multiset `Z` of (candidate) zeros:
`λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.  This is the standard Bombieri–Lagarias
expression of Li's coefficients as a sum over the zeros. -/
noncomputable def liCoeff (Z : Multiset ℂ) (n : ℕ) : ℝ :=
  (Z.map fun ρ : ℂ => 1 - ((1 - 1 / ρ) ^ n).re).sum

/-- The set of nontrivial zeros of the Riemann zeta function, in the sense used by
Mathlib's `RiemannHypothesis`. -/
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1}

/-! ## The critical line and the Möbius transformation `ρ ↦ 1 - 1/ρ` -/

private theorem sq_norm_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-- For `ρ ≠ 0`, the point `ρ` lies on the critical line iff its image `1 - 1/ρ` under the
Möbius transformation carrying the critical line to the unit circle has modulus `1`. -/
theorem re_eq_half_iff_norm_eq_one {ρ : ℂ} (hρ : ρ ≠ 0) :
    ρ.re = 1 / 2 ↔ ‖1 - 1 / ρ‖ = 1 := by
  have hn : ‖ρ‖ ≠ 0 := by simpa using hρ
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div, div_eq_one_iff_eq hn]
  have key : ‖ρ - 1‖ = ‖ρ‖ ↔ ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
    constructor
    · intro h; rw [h]
    · intro h; nlinarith [norm_nonneg (ρ - 1), norm_nonneg ρ]
  rw [key, sq_norm_re_im, sq_norm_re_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith [h]

/-- The Möbius image is nonzero as soon as `ρ ∉ {0, 1}`. -/
theorem moebius_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : 1 - 1 / ρ ≠ 0 := by
  intro h
  have h2 : (1 : ℂ) = 1 / ρ := sub_eq_zero.1 h
  apply h1
  field_simp at h2
  exact h2

/-- The functional-equation involution `ρ ↦ 1 - ρ` inverts the Möbius image. -/
theorem moebius_one_sub {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (1 - 1 / (1 - ρ)) * (1 - 1 / ρ) = 1 := by
  have h2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  field_simp
  ring

/-! ## A simultaneous approximation lemma -/

/-- Simultaneous Dirichlet-type approximation: for finitely many complex numbers of modulus
one there are arbitrarily large exponents `n` making all the powers `w i ^ n` simultaneously
close to `1`. -/
theorem exists_pow_near_one {ι : Type} [Fintype ι] (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∀ i, ‖w i ^ n - 1‖ ≤ ε := by
  classical
  set M := N + 1 with hM
  set g : ℕ → (ι → ℂ) := fun k i => w i ^ (M * k) with hg
  have hmem : ∀ k, g k ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 ?_
    intro i
    simp [hg, norm_pow, hw i]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hmem
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
  have hpq : dist (g (φ (K + 1))) (g (φ K)) ≤ ε := le_of_lt (hK (K + 1) (by omega) K (by omega))
  have hlt : φ K < φ (K + 1) := hφ (Nat.lt_succ_self K)
  have hone : 1 ≤ φ (K + 1) - φ K := by omega
  refine ⟨M * (φ (K + 1) - φ K), ?_, ?_, ?_⟩
  · calc N ≤ M := by omega
      _ = M * 1 := by ring
      _ ≤ M * (φ (K + 1) - φ K) := Nat.mul_le_mul_left M hone
  · have : 1 * 1 ≤ M * (φ (K + 1) - φ K) := Nat.mul_le_mul (by omega) hone
    omega
  · intro i
    have hd : dist (g (φ (K + 1)) i) (g (φ K) i) ≤ ε := le_trans (dist_le_pi_dist _ _ i) hpq
    have hexp : M * φ K + M * (φ (K + 1) - φ K) = M * φ (K + 1) := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hlt.le]
    have hsplit : w i ^ (M * φ (K + 1)) - w i ^ (M * φ K)
        = w i ^ (M * φ K) * (w i ^ (M * (φ (K + 1) - φ K)) - 1) := by
      rw [mul_sub, ← pow_add, hexp, mul_one]
    have hnorm : ‖w i ^ (M * φ (K + 1)) - w i ^ (M * φ K)‖
        = ‖w i ^ (M * (φ (K + 1) - φ K)) - 1‖ := by
      rw [hsplit, norm_mul, norm_pow, hw i, one_pow, one_mul]
    rw [Complex.dist_eq] at hd
    simp only [hg] at hd
    rw [← hnorm]
    exact hd

/-! ## The abstract Li criterion -/

/-- **Easy direction.**  If the Möbius image of every element of `Z` has modulus one — i.e. every
element of `Z` lies on the critical line — then all Li coefficients of `Z` are nonnegative. -/
theorem liCoeff_nonneg_of_norm_eq_one {Z : Multiset ℂ} (h : ∀ ρ ∈ Z, ‖1 - 1 / ρ‖ = 1) (n : ℕ) :
    0 ≤ liCoeff Z n := by
  apply Multiset.sum_nonneg
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨ρ, hρ, rfl⟩ := hx
  have hle : ((1 - 1 / ρ) ^ n).re ≤ ‖(1 - 1 / ρ) ^ n‖ := Complex.re_le_norm _
  rw [norm_pow, h ρ hρ, one_pow] at hle
  linarith

/-- **Hard direction.**  If some element of `Z` has a Möbius image of modulus `> 1`, then some
Li coefficient of `Z` is strictly negative. -/
theorem exists_liCoeff_neg {Z : Multiset ℂ} (h0 : ∀ ρ ∈ Z, ρ ≠ 0) (h1 : ∀ ρ ∈ Z, ρ ≠ 1)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z) (hR : 1 < ‖1 - 1 / ρ₀‖) :
    ∃ n : ℕ, 1 ≤ n ∧ liCoeff Z n < 0 := by
  classical
  set m : ℝ := (Multiset.card Z : ℝ) with hm
  set R : ℝ := ‖1 - 1 / ρ₀‖ with hRdef
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * (m + 1)) hR
  set ι := {x : ℂ // x ∈ Z.toFinset} with hι
  set w : ι → ℂ := fun i => (1 - 1 / (i : ℂ)) / ‖1 - 1 / (i : ℂ)‖ with hw
  have hmemZ : ∀ i : ι, (i : ℂ) ∈ Z := fun i => Multiset.mem_toFinset.mp i.2
  have hzne : ∀ i : ι, 1 - 1 / (i : ℂ) ≠ 0 := fun i =>
    moebius_ne_zero (h0 _ (hmemZ i)) (h1 _ (hmemZ i))
  have hwnorm : ∀ i : ι, ‖w i‖ = 1 := by
    intro i
    rw [hw]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (by simpa using hzne i)
  obtain ⟨n, hnN, hn1, hnear⟩ := exists_pow_near_one w hwnorm (by norm_num : (0:ℝ) < 1 / 2) N
  -- Pointwise upper bound on the summands.
  have key : ∀ ρ ∈ Z, 1 - ((1 - 1 / ρ) ^ n).re ≤ 1 - ‖1 - 1 / ρ‖ ^ n / 2 := by
    intro ρ hρ
    have hmem : ρ ∈ Z.toFinset := Multiset.mem_toFinset.mpr hρ
    have hznz : ‖1 - 1 / ρ‖ ≠ 0 := by
      simpa using moebius_ne_zero (h0 _ hρ) (h1 _ hρ)
    have hcnz : ((‖1 - 1 / ρ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hznz
    have hz : (1 - 1 / ρ) = (‖1 - 1 / ρ‖ : ℂ) * w ⟨ρ, hmem⟩ := by
      have hwi : w ⟨ρ, hmem⟩ = (1 - 1 / ρ) / (‖1 - 1 / ρ‖ : ℂ) := rfl
      rw [hwi]
      field_simp
    have hre : (1 : ℝ) / 2 ≤ ((w ⟨ρ, hmem⟩) ^ n).re := by
      have ha : (1 - (w ⟨ρ, hmem⟩) ^ n).re ≤ ‖1 - (w ⟨ρ, hmem⟩) ^ n‖ := Complex.re_le_norm _
      have hb : ‖1 - (w ⟨ρ, hmem⟩) ^ n‖ = ‖(w ⟨ρ, hmem⟩) ^ n - 1‖ := by rw [norm_sub_rev]
      have hc := hnear ⟨ρ, hmem⟩
      rw [← hb] at hc
      simp only [Complex.sub_re, Complex.one_re] at ha
      linarith
    have hpow : ((1 - 1 / ρ) ^ n).re = ‖1 - 1 / ρ‖ ^ n * ((w ⟨ρ, hmem⟩) ^ n).re := by
      rw [hz, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rw [hpow]
    have hpos : (0 : ℝ) ≤ ‖1 - 1 / ρ‖ ^ n := by positivity
    nlinarith [hre, hpos]
  refine ⟨n, hn1, ?_⟩
  -- Split off the offending zero `ρ₀` and bound the remaining terms by `1` each.
  have hZeq : Z = ρ₀ ::ₘ Z.erase ρ₀ := (Multiset.cons_erase hρ₀).symm
  have hsum : (Multiset.map (fun ρ : ℂ => 1 - ((1 - 1 / ρ) ^ n).re) (Z.erase ρ₀)).sum
      ≤ (Multiset.card (Z.erase ρ₀) : ℝ) := by
    calc (Multiset.map (fun ρ : ℂ => 1 - ((1 - 1 / ρ) ^ n).re) (Z.erase ρ₀)).sum
        ≤ (Multiset.map (fun _ : ℂ => (1 : ℝ)) (Z.erase ρ₀)).sum := by
          refine Multiset.sum_map_le_sum_map _ _ ?_
          intro ρ hρ
          have h := key ρ (Multiset.mem_of_mem_erase hρ)
          have : (0 : ℝ) ≤ ‖1 - 1 / ρ‖ ^ n / 2 := by positivity
          linarith
      _ = (Multiset.card (Z.erase ρ₀) : ℝ) := by
          simp [Multiset.map_const', Multiset.sum_replicate]
  have hcard : ((Multiset.card (Z.erase ρ₀) : ℕ) : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast Multiset.card_erase_le
  have hexp : liCoeff Z n = (1 - ((1 - 1 / ρ₀) ^ n).re)
      + (Multiset.map (fun ρ : ℂ => 1 - ((1 - 1 / ρ) ^ n).re) (Z.erase ρ₀)).sum := by
    rw [liCoeff]
    conv_lhs => rw [hZeq]
    rw [Multiset.map_cons, Multiset.sum_cons]
  have hRn : R ^ N ≤ R ^ n := pow_le_pow_right₀ hR.le hnN
  have hbig : m + 1 < R ^ n / 2 := by linarith
  rw [hexp]
  have hk0 := key ρ₀ hρ₀
  rw [← hRdef] at hk0
  linarith

/-- **The Li criterion for a finite symmetric family of zeros.**

Let `Z` be a finite multiset of nonzero complex numbers which is invariant (with multiplicity)
under the functional-equation involution `ρ ↦ 1 - ρ`.  Then every element of `Z` lies on the
critical line `Re s = 1/2` if and only if all the Li coefficients `λ_n(Z)`, `n ≥ 1`, are
nonnegative. -/
theorem li_criterion {Z : Multiset ℂ} (h0 : ∀ ρ ∈ Z, ρ ≠ 0)
    (hsym : Z.map (fun ρ : ℂ => 1 - ρ) = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff Z n := by
  have hmem : ∀ ρ ∈ Z, 1 - ρ ∈ Z := by
    intro ρ hρ
    have : (1 - ρ) ∈ Z.map (fun ρ : ℂ => 1 - ρ) := Multiset.mem_map_of_mem _ hρ
    rwa [hsym] at this
  have h1 : ∀ ρ ∈ Z, ρ ≠ 1 := by
    intro ρ hρ hcon
    have : (1 : ℂ) - ρ ∈ Z := hmem ρ hρ
    rw [hcon, sub_self] at this
    exact h0 0 this rfl
  constructor
  · intro h n _
    refine liCoeff_nonneg_of_norm_eq_one ?_ n
    intro ρ hρ
    exact (re_eq_half_iff_norm_eq_one (h0 ρ hρ)).1 (h ρ hρ)
  · intro h ρ hρ
    rw [re_eq_half_iff_norm_eq_one (h0 ρ hρ)]
    -- The Möbius image cannot have modulus `> 1` …
    have hno : ∀ σ ∈ Z, ¬ (1 < ‖1 - 1 / σ‖) := by
      intro σ hσ hgt
      obtain ⟨n, hn1, hneg⟩ := exists_liCoeff_neg h0 h1 hσ hgt
      exact absurd (h n hn1) (not_le.2 hneg)
    -- … and by the symmetry `ρ ↦ 1 - ρ` it cannot have modulus `< 1` either.
    have hprod := moebius_one_sub (h0 ρ hρ) (h1 ρ hρ)
    have hnorms : ‖1 - 1 / (1 - ρ)‖ * ‖1 - 1 / ρ‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    have hle₁ : ‖1 - 1 / ρ‖ ≤ 1 := not_lt.1 (hno ρ hρ)
    have hle₂ : ‖1 - 1 / (1 - ρ)‖ ≤ 1 := not_lt.1 (hno _ (hmem ρ hρ))
    have hpos : 0 < ‖1 - 1 / ρ‖ := by
      have := moebius_ne_zero (h0 ρ hρ) (h1 ρ hρ)
      positivity
    nlinarith [hnorms, hle₁, hle₂, hpos]

/-! ## Nontrivial zeros of `ζ` -/

/-- `ζ` does not vanish at the negative odd integers. -/
theorem zeta_neg_odd_ne_zero (k : ℕ) : riemannZeta (-(2 * (k : ℂ) + 1)) ≠ 0 := by
  have hre : ((2 * (k : ℂ) + 2)).re = 2 * (k : ℝ) + 2 := by
    simp
  have hne : ∀ n : ℕ, (2 * (k : ℂ) + 2) ≠ -(n : ℂ) := by
    intro n hcon
    have := congrArg Complex.re hcon
    rw [hre] at this
    simp at this
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne1 : (2 * (k : ℂ) + 2) ≠ 1 := by
    intro hcon
    have := congrArg Complex.re hcon
    rw [hre] at this
    simp at this
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfe := riemannZeta_one_sub hne hne1
  have harg : (1 : ℂ) - (2 * (k : ℂ) + 2) = -(2 * (k : ℂ) + 1) := by ring
  rw [harg] at hfe
  rw [hfe]
  -- every factor is nonzero
  have hcos : Complex.cos (↑π * (2 * (k : ℂ) + 2) / 2) ≠ 0 := by
    have : (↑π * (2 * (k : ℂ) + 2) / 2) = ((k : ℂ) + 1) * ↑π := by ring
    rw [this]
    have hnat : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hnat, Complex.cos_nat_mul_pi]
    exact pow_ne_zero _ (by norm_num)
  have hgamma : Complex.Gamma (2 * (k : ℂ) + 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero ?_
    intro n
    exact hne n
  have hcpow : ((2 * (π : ℂ)) ^ (-(2 * (k : ℂ) + 2))) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_ |>.2
    · simp [Real.pi_ne_zero]
    · intro hcon
      have := congrArg Complex.re hcon
      simp at this
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  have hzeta : riemannZeta (2 * (k : ℂ) + 2) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [hre]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨⟨⟨two_ne_zero, hcpow⟩, hgamma⟩, hcos⟩, hzeta⟩

/-- A nontrivial zero of `ζ` is never a nonpositive integer. -/
theorem nontrivialZeros_ne_neg_nat {s : ℂ} (hs : s ∈ nontrivialZeros) (n : ℕ) : s ≠ -(n : ℂ) := by
  obtain ⟨hz, htriv, -⟩ := hs
  intro hcon
  subst hcon
  rcases Nat.even_or_odd n with he | ho
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, neg_zero, riemannZeta_zero] at hz
      norm_num at hz
    · obtain ⟨j, hj⟩ := he
      have hjpos : 1 ≤ j := by omega
      obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact htriv ⟨i, by rw [hj, hi]; push_cast; ring⟩
  · obtain ⟨i, hi⟩ := ho
    apply zeta_neg_odd_ne_zero i
    rw [← hz, hi]
    push_cast
    ring_nf

/-- Nontrivial zeros are nonzero. -/
theorem nontrivialZeros_ne_zero {s : ℂ} (hs : s ∈ nontrivialZeros) : s ≠ 0 := by
  have := nontrivialZeros_ne_neg_nat hs 0
  simpa using this

/-- The set of nontrivial zeros is invariant under the functional-equation involution
`s ↦ 1 - s`. -/
theorem one_sub_mem_nontrivialZeros {s : ℂ} (hs : s ∈ nontrivialZeros) :
    1 - s ∈ nontrivialZeros := by
  obtain ⟨hz, htriv, hne1⟩ := hs
  have hsne : ∀ n : ℕ, s ≠ -(n : ℂ) := nontrivialZeros_ne_neg_nat ⟨hz, htriv, hne1⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub hsne hne1, hz, mul_zero]
  · rintro ⟨n, hn⟩
    -- then `s = 2n + 3`, which has real part `≥ 1`, so `ζ s ≠ 0`
    have hs' : s = 2 * (n : ℂ) + 3 := by
      have : s = 1 - (-2 * ((n : ℂ) + 1)) := by rw [← hn]; ring
      rw [this]; ring
    refine riemannZeta_ne_zero_of_one_le_re ?_ hz
    rw [hs']
    simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro hcon
    have : s = 0 := by
      have := sub_eq_self.1 (by linear_combination hcon : (1 : ℂ) - s = 1 - 0 + s - s)
      linarith [this]
    exact nontrivialZeros_ne_zero ⟨hz, htriv, hne1⟩ this

/-! ## The main theorem -/

/-- **Li's criterion for the Riemann Hypothesis.**

The Riemann Hypothesis holds if and only if, for every finite family `Z` of nontrivial zeros of
`ζ` that is invariant (with multiplicity) under the functional-equation involution `ρ ↦ 1 - ρ`,
all the Li coefficients `λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`, `n ≥ 1`, are nonnegative. -/
theorem RH_Li_criterion :
    RiemannHypothesis ↔
      ∀ Z : Multiset ℂ, (∀ ρ ∈ Z, ρ ∈ nontrivialZeros) →
        Z.map (fun ρ : ℂ => 1 - ρ) = Z → ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff Z n := by
  constructor
  · intro hRH Z hZ hsym
    refine (li_criterion (fun ρ hρ => nontrivialZeros_ne_zero (hZ ρ hρ)) hsym).1 ?_
    intro ρ hρ
    obtain ⟨hz, htriv, hne1⟩ := hZ ρ hρ
    exact hRH ρ hz htriv hne1
  · intro H s hz htriv hne1
    have hs : s ∈ nontrivialZeros := ⟨hz, htriv, hne1⟩
    have hs' : 1 - s ∈ nontrivialZeros := one_sub_mem_nontrivialZeros hs
    set Z : Multiset ℂ := s ::ₘ (1 - s) ::ₘ 0 with hZdef
    have hZmem : ∀ ρ ∈ Z, ρ ∈ nontrivialZeros := by
      intro ρ hρ
      rw [hZdef] at hρ
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact hs
      · exact hs'
    have hsym : Z.map (fun ρ : ℂ => 1 - ρ) = Z := by
      rw [hZdef]
      simp only [Multiset.map_cons, Multiset.map_zero]
      rw [show (1 : ℂ) - (1 - s) = s by ring]
      exact Multiset.cons_swap _ _ _
    have hcrit := (li_criterion (fun ρ hρ => nontrivialZeros_ne_zero (hZmem ρ hρ)) hsym).2
      (H Z hZmem hsym)
    exact hcrit s (by rw [hZdef]; simp)

end Frontier

