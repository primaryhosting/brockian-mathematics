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
