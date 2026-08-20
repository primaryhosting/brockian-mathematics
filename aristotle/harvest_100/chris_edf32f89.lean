/-
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
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

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of "configurations" of size `N` at modulus `q`: ordered pairs `(a, b)` with
`a, b < N` and `a ≡ b [MOD q]`. -/
def configCount (q N : ℕ) : ℕ :=
  ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 % q = p.2 % q)).card

/-- The expected main term for `configCount q N`, namely `N ^ 2 / q`. -/
noncomputable def mainTerm (q N : ℕ) : ℝ := (N : ℝ) ^ 2 / (q : ℝ)

/-- In `[0, N)` there are at most `N / q + 1` integers in a fixed residue class mod `q`. -/
lemma card_residue_le (q N r : ℕ) :
    ((Finset.range N).filter (fun b => b % q = r)).card ≤ N / q + 1 := by
  classical
  have h : ((Finset.range N).filter (fun b => b % q = r)).card
      ≤ (Finset.range (N / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun b => b / q)
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
      simp only [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hb.1.le)
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      have hxy' : x / q = y / q := hxy
      have hx' : q * (x / q) + x % q = x := Nat.div_add_mod x q
      have hy' : q * (y / q) + y % q = y := Nat.div_add_mod y q
      calc x = q * (x / q) + x % q := hx'.symm
        _ = q * (y / q) + y % q := by rw [hxy', hx.2, hy.2]
        _ = y := hy'
  simpa using h

/-- In `[0, N)` there are at least `N / q` integers in a fixed residue class mod `q`. -/
lemma le_card_residue (q N r : ℕ) (hr : r < q) :
    N / q ≤ ((Finset.range N).filter (fun b => b % q = r)).card := by
  classical
  have h : (Finset.range (N / q)).card
      ≤ ((Finset.range N).filter (fun b => b % q = r)).card := by
    apply Finset.card_le_card_of_injOn (fun k => q * k + r)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, by simp [Nat.mod_eq_of_lt hr]⟩
      have h1 : q * (k + 1) ≤ q * (N / q) := Nat.mul_le_mul_left q hk
      have h2 : q * (N / q) ≤ N := Nat.mul_div_le N q
      have h3 : q * k + q = q * (k + 1) := by ring
      omega
    · intro x _ y _ hxy
      have hxy' : q * x + r = q * y + r := hxy
      have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le r) hr
      have : q * x = q * y := by omega
      exact Nat.eq_of_mul_eq_mul_left hq this
  simpa using h

/-- Fiberwise decomposition of `configCount`. -/
lemma configCount_eq_sum (q N : ℕ) :
    configCount q N
      = ∑ a ∈ Finset.range N, ((Finset.range N).filter (fun b => b % q = a % q)).card := by
  classical
  rw [configCount, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun b _ => if_congr eq_comm rfl rfl

lemma configCount_le (q N : ℕ) :
    configCount q N ≤ N * (N / q + 1) := by
  rw [configCount_eq_sum]
  calc ∑ a ∈ Finset.range N, ((Finset.range N).filter (fun b => b % q = a % q)).card
      ≤ ∑ _a ∈ Finset.range N, (N / q + 1) :=
        Finset.sum_le_sum (fun a _ => card_residue_le q N (a % q))
    _ = N * (N / q + 1) := by simp

lemma le_configCount (q N : ℕ) (hq : 0 < q) :
    N * (N / q) ≤ configCount q N := by
  rw [configCount_eq_sum]
  calc N * (N / q) = ∑ _a ∈ Finset.range N, (N / q) := by simp
    _ ≤ ∑ a ∈ Finset.range N, ((Finset.range N).filter (fun b => b % q = a % q)).card :=
        Finset.sum_le_sum (fun a _ => le_card_residue q N (a % q) (Nat.mod_lt _ hq))

/-- The configuration count differs from the main term by at most `N`. -/
lemma abs_configCount_sub_main_le (q N : ℕ) (hq : 0 < q) :
    |(configCount q N : ℝ) - (N : ℝ) ^ 2 / (q : ℝ)| ≤ (N : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  set D : ℝ := ((N / q : ℕ) : ℝ) with hD
  have hDnn : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hdiv1 : (q : ℝ) * D ≤ (N : ℝ) := by
    rw [hD]; exact_mod_cast Nat.mul_div_le N q
  have hdiv2 : (N : ℝ) < (q : ℝ) * (D + 1) := by
    have h := Nat.lt_mul_div_succ N hq
    rw [hD]
    exact_mod_cast h
  have hup : (configCount q N : ℝ) ≤ (N : ℝ) * (D + 1) := by
    have h : ((configCount q N : ℕ) : ℝ) ≤ ((N * (N / q + 1) : ℕ) : ℝ) := by
      exact_mod_cast configCount_le q N
    rw [hD]
    push_cast at h ⊢
    linarith
  have hlo : (N : ℝ) * D ≤ (configCount q N : ℝ) := by
    have h : ((N * (N / q) : ℕ) : ℝ) ≤ ((configCount q N : ℕ) : ℝ) := by
      exact_mod_cast le_configCount q N hq
    rw [hD]
    push_cast at h ⊢
    linarith
  rw [abs_le]
  constructor
  · have h : (N : ℝ) ^ 2 / (q : ℝ) ≤ (N : ℝ) * D + (N : ℝ) := by
      rw [div_le_iff₀ hq0]
      nlinarith
    linarith
  · have h : (N : ℝ) * D ≤ (N : ℝ) ^ 2 / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      nlinarith
    linarith

/-- **Main result.** For a fixed modulus `q > 0`, the number of configurations of size `N`
divided by the main term `N ^ 2 / q` tends to `1` as `N → ∞`. -/
theorem configCount_over_main_tendsto (q : ℕ) (hq : 0 < q) :
    Filter.Tendsto (fun N : ℕ => (configCount q N : ℝ) / mainTerm q N)
      Filter.atTop (nhds 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have key : Filter.Tendsto
      (fun N : ℕ => (configCount q N : ℝ) / mainTerm q N - 1) Filter.atTop (nhds 0) := by
    have hbound : ∀ᶠ N : ℕ in Filter.atTop,
        ‖(configCount q N : ℝ) / mainTerm q N - 1‖ ≤ (q : ℝ) / (N : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hmain : mainTerm q N = (N : ℝ) ^ 2 / (q : ℝ) := rfl
      have hmpos : (0 : ℝ) < (N : ℝ) ^ 2 / (q : ℝ) := by positivity
      have h := abs_configCount_sub_main_le q N hq
      rw [Real.norm_eq_abs, hmain, div_sub_one hmpos.ne', abs_div, abs_of_pos hmpos,
        div_le_div_iff₀ hmpos hN0]
      have hqm : (q : ℝ) * ((N : ℝ) ^ 2 / (q : ℝ)) = (N : ℝ) ^ 2 := by
        field_simp
      rw [hqm]
      calc |(configCount q N : ℝ) - (N : ℝ) ^ 2 / (q : ℝ)| * (N : ℝ)
          ≤ (N : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right h hN0.le
        _ = (N : ℝ) ^ 2 := by ring
    refine squeeze_zero_norm' hbound ?_
    exact tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)
  have h := key.add_const 1
  simpa using h

end EquidistributionBVReduction
end Brockian

