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

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The set of *configurations* of size `N` in the residue class `r` modulo `q`:
pairs `(a, b)` with `a, b < N` and `a + b ≡ r [MOD q]`. -/
def configFinset (q r N : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ Finset.range N ×ˢ Finset.range N | (p.1 + p.2) % q = r % q}

/-- The number of configurations of size `N` in the residue class `r` modulo `q`. -/
def configCount (q r N : ℕ) : ℕ := (configFinset q r N).card

/-- The expected main term for `configCount q r N`: the box `[0, N)²` contains `N²` points,
and each of the `q` residue classes should receive an equal share of them. -/
noncomputable def mainTerm (q N : ℕ) : ℝ := (N : ℝ) ^ 2 / (q : ℝ)

/-- Reformulating the congruence `a + b ≡ r [MOD q]` as a congruence on `b` alone. -/
lemma mem_config_iff (q r a b : ℕ) (hq : 0 < q) :
    (a + b) % q = r % q ↔ b % q = (r + (q - 1) * a) % q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : (a + b + m * a) % (m + 1) = b % (m + 1) := by
    rw [show a + b + m * a = b + (m + 1) * a by ring]
    exact Nat.add_mul_mod_self_left _ _ _
  constructor
  · intro h
    have h2 : (a + b + m * a) % (m + 1) = (r + m * a) % (m + 1) :=
      Nat.ModEq.add_right (m * a) h
    rwa [key] at h2
  · intro h
    have h2 : (a + b + m * a) % (m + 1) = (r + m * a) % (m + 1) := by rw [key]; exact h
    exact Nat.ModEq.add_right_cancel' (m * a) h2

/-- Counting the elements of `[0, N)` lying in a fixed residue class modulo `q`. -/
lemma card_filter_residue (q v N : ℕ) (hq : 0 < q) :
    {b ∈ Finset.range N | b % q = v % q}.card = N / q + (if v % q < N % q then 1 else 0) := by
  have h := Nat.count_modEq_card N hq v
  rw [Nat.count_eq_card_filter_range] at h
  rw [← h]
  rfl

/-- Slicing the configuration count along the first coordinate turns it into a sum of
residue-class counts. -/
lemma configCount_eq_sum (q r N : ℕ) (hq : 0 < q) :
    configCount q r N =
      ∑ a ∈ Finset.range N, (N / q + (if (r + (q - 1) * a) % q < N % q then 1 else 0)) := by
  unfold configCount configFinset
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← card_filter_residue q (r + (q - 1) * a) N hq, Finset.card_filter]
  exact Finset.sum_congr rfl (fun b _ => by simp only [mem_config_iff q r a b hq])

/-- The configuration count is squeezed between `N * (N / q)` and `N * (N / q) + N`. -/
lemma configCount_bounds (q r N : ℕ) (hq : 0 < q) :
    N * (N / q) ≤ configCount q r N ∧ configCount q r N ≤ N * (N / q) + N := by
  rw [configCount_eq_sum q r N hq]
  constructor
  · calc N * (N / q) = ∑ _a ∈ Finset.range N, N / q := by simp
    _ ≤ _ := Finset.sum_le_sum (fun a _ => Nat.le_add_right _ _)
  · calc ∑ a ∈ Finset.range N, (N / q + (if (r + (q - 1) * a) % q < N % q then 1 else 0))
        ≤ ∑ _a ∈ Finset.range N, (N / q + 1) :=
        Finset.sum_le_sum (fun a _ => by split <;> omega)
    _ = N * (N / q) + N := by simp [Nat.mul_add]

/-- Two-sided bound for the ratio `configCount / mainTerm`. -/
lemma ratio_bounds (q r N : ℕ) (hq : 0 < q) (hN : 0 < N) :
    ((N : ℝ) - q) / N ≤ (configCount q r N : ℝ) / mainTerm q N ∧
      (configCount q r N : ℝ) / mainTerm q N ≤ ((N : ℝ) + q) / N := by
  obtain ⟨hlow, hhigh⟩ := configCount_bounds q r N hq
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hd1 : (q : ℝ) * ((N / q : ℕ) : ℝ) ≤ (N : ℝ) := by
    have : q * (N / q) ≤ N := Nat.mul_div_le N q
    exact_mod_cast this
  have hd2 : (N : ℝ) ≤ (q : ℝ) * ((N / q : ℕ) : ℝ) + q := by
    have : N ≤ q * (N / q) + q := by
      have h := Nat.div_add_mod N q
      have h2 : N % q < q := Nat.mod_lt _ hq
      omega
    exact_mod_cast this
  have hlowR : (N : ℝ) * ((N / q : ℕ) : ℝ) ≤ (configCount q r N : ℝ) := by exact_mod_cast hlow
  have hhighR : (configCount q r N : ℝ) ≤ (N : ℝ) * ((N / q : ℕ) : ℝ) + N := by exact_mod_cast hhigh
  have hratio :
      (configCount q r N : ℝ) / mainTerm q N = (configCount q r N : ℝ) * q / (N : ℝ) ^ 2 := by
    show (configCount q r N : ℝ) / ((N : ℝ) ^ 2 / q) = _
    field_simp
  rw [hratio]
  generalize ((N / q : ℕ) : ℝ) = d at hd1 hd2 hlowR hhighR
  generalize ((configCount q r N : ℕ) : ℝ) = C at hlowR hhighR ⊢
  have hsq : (0:ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have hqN : (0:ℝ) ≤ (q : ℝ) * N := by positivity
  constructor
  · rw [div_le_div_iff₀ hNR (by positivity)]
    have h3 : (N : ℝ) ^ 2 * N ≤ (N : ℝ) ^ 2 * ((q : ℝ) * d + q) := mul_le_mul_of_nonneg_left hd2 hsq
    have h4 : ((N : ℝ) * d) * ((q : ℝ) * N) ≤ C * ((q : ℝ) * N) :=
      mul_le_mul_of_nonneg_right hlowR hqN
    nlinarith [h3, h4]
  · rw [div_le_div_iff₀ (by positivity) hNR]
    have h3 : (N : ℝ) ^ 2 * ((q : ℝ) * d) ≤ (N : ℝ) ^ 2 * N := mul_le_mul_of_nonneg_left hd1 hsq
    have h4 : C * ((q : ℝ) * N) ≤ ((N : ℝ) * d + N) * ((q : ℝ) * N) :=
      mul_le_mul_of_nonneg_right hhighR hqN
    nlinarith [h3, h4]

/-- The lower comparison sequence `(N - q) / N` tends to `1`. -/
lemma tendsto_sub_div (q : ℕ) : Tendsto (fun N : ℕ => ((N : ℝ) - q) / N) atTop (nhds 1) := by
  have h : ∀ᶠ N : ℕ in atTop, ((N : ℝ) - q) / N = 1 - (q : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  rw [tendsto_congr' h]
  simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ))

/-- The upper comparison sequence `(N + q) / N` tends to `1`. -/
lemma tendsto_add_div (q : ℕ) : Tendsto (fun N : ℕ => ((N : ℝ) + q) / N) atTop (nhds 1) := by
  have h : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + q) / N = 1 + (q : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  rw [tendsto_congr' h]
  simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).add
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ))

/-- **Equidistribution of configurations.** For a fixed modulus `q > 0` and residue `r`, the
number of pairs `(a, b) ∈ [0, N)²` with `a + b ≡ r [MOD q]`, divided by the main term `N² / q`,
tends to `1` as `N → ∞`. -/
theorem configCount_over_main_tendsto (q r : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (configCount q r N : ℝ) / mainTerm q N) atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_sub_div q) (tendsto_add_div q)
    ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN using (ratio_bounds q r N hq hN).1
  · filter_upwards [eventually_gt_atTop 0] with N hN using (ratio_bounds q r N hq hN).2

end Brockian.EquidistributionBVReduction

