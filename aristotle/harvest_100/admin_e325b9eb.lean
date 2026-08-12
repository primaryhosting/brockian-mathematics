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

namespace Brockian

/-! ## The twin-prime singular series and an effective rate of convergence

We study the Hardy–Littlewood singular series for prime pairs,
`𝔖 = 2 * ∏_{p odd prime} (1 - 1/(p-1)^2)`,
realised as the limit of its truncations `𝔖(N) = 2 * ∏_{p ≤ N, p odd prime} (1 - 1/(p-1)^2)`.

The main result `Brockian.SingularSeriesConvergenceRate` is an *effective* bound on the
error committed by truncating at `N`:  `|𝔖(N) - 𝔖| ≤ 2 / (N - 1)`. -/

/-- The local factor exponent: `sTerm p = 1/(p-1)^2` for an odd prime `p`, and `0` otherwise. -/
noncomputable def sTerm (p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 then 1 / ((p : ℝ) - 1) ^ 2 else 0

lemma sTerm_nonneg (p : ℕ) : 0 ≤ sTerm p := by
  unfold sTerm
  split
  · positivity
  · exact le_rfl

/-- An odd prime is at least `3`. -/
lemma three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

lemma sTerm_le_one (p : ℕ) : sTerm p ≤ 1 := by
  unfold sTerm
  split
  · rename_i h
    have h3 : 3 ≤ p := three_le_of_prime_ne_two h.1 h.2
    have hx : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    rw [div_le_one (by nlinarith)]
    nlinarith
  · norm_num

/-- The key telescoping estimate: `1/(p-1)^2 ≤ 1/(p-2) - 1/(p-1)` for `p ≥ 3`. -/
lemma sTerm_le_telescope {p : ℕ} (hp : 3 ≤ p) :
    sTerm p ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have hx : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  unfold sTerm
  split
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · positivity

/-- Telescoping bound for a block of terms. -/
lemma tail_sum_le (N : ℕ) (hN : 2 ≤ N) :
    ∀ M : ℕ, N + 1 ≤ M →
      ∑ p ∈ Finset.Ico (N + 1) M, sTerm p ≤ 1 / ((N : ℝ) - 1) - 1 / ((M : ℝ) - 2) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
      have : ((N : ℝ) + 1) - 2 = (N : ℝ) - 1 := by ring
      simp [this]
  | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have h3 : 3 ≤ M := by omega
      have hstep := sTerm_le_telescope h3
      have hcast : ((M : ℝ) + 1) - 2 = (M : ℝ) - 1 := by ring
      push_cast
      rw [hcast]
      have := ih
      linarith

/-- The tail of the sum of local exponents beyond `N` is at most `1/(N-1)`. -/
lemma tail_sum_le_bound (N M : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Finset.Ico (N + 1) M, sTerm p ≤ 1 / ((N : ℝ) - 1) := by
  rcases lt_or_ge M (N + 1) with h | h
  · rw [Finset.Ico_eq_empty (by omega)]
    have : (1 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    simp only [Finset.sum_empty]
    positivity
  · have h1 := tail_sum_le N hN M h
    have h2 : (0 : ℝ) < (M : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 3 ≤ M)
      linarith
    have : 0 < 1 / ((M : ℝ) - 2) := by positivity
    linarith

/-- Weierstrass-type inequality: `∏ (1 - a i) ≥ 1 - ∑ a i` for `0 ≤ a i ≤ 1`. -/
lemma one_sub_sum_le_prod_one_sub (s : Finset ℕ) (a : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have h0' : ∀ i ∈ s, 0 ≤ a i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, a i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg h0'
      have hja : a j ≤ 1 := h1 j (Finset.mem_insert_self j s)
      have hja0 : 0 ≤ a j := h0 j (Finset.mem_insert_self j s)
      have key := ih h0' h1'
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      have hmul : (1 - a j) * (1 - ∑ i ∈ s, a i) ≤ (1 - a j) * ∏ i ∈ s, (1 - a i) :=
        mul_le_mul_of_nonneg_left key (by linarith)
      nlinarith

/-- The truncated Euler product `∏_{p ≤ N} (1 - sTerm p)`. -/
noncomputable def partialProduct (N : ℕ) : ℝ :=
  ∏ p ∈ Finset.range (N + 1), (1 - sTerm p)

lemma partialProduct_nonneg (N : ℕ) : 0 ≤ partialProduct N := by
  refine Finset.prod_nonneg ?_
  intro i _
  have := sTerm_le_one i
  linarith

lemma partialProduct_le_one (N : ℕ) : partialProduct N ≤ 1 := by
  refine Finset.prod_le_one ?_ ?_ <;> intro i _
  · have := sTerm_le_one i; linarith
  · have := sTerm_nonneg i; linarith

/-- Splitting the truncated product at `N`. -/
lemma partialProduct_split {N M : ℕ} (h : N ≤ M) :
    partialProduct M = partialProduct N * ∏ p ∈ Finset.Ico (N + 1) (M + 1), (1 - sTerm p) := by
  unfold partialProduct
  rw [Finset.prod_range_mul_prod_Ico _ (by omega : N + 1 ≤ M + 1)]

lemma partialProduct_antitone : Antitone partialProduct := by
  intro N M h
  rw [partialProduct_split h]
  have hle : ∏ p ∈ Finset.Ico (N + 1) (M + 1), (1 - sTerm p) ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_ <;> intro i _
    · have := sTerm_le_one i; linarith
    · have := sTerm_nonneg i; linarith
  nlinarith [partialProduct_nonneg N]

/-- Effective two-sided comparison of truncations: for `M ≥ N ≥ 2`, the truncation at `M`
differs from the truncation at `N` by at most `1/(N-1)`. -/
lemma partialProduct_sub_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    partialProduct N - 1 / ((N : ℝ) - 1) ≤ partialProduct M := by
  have hprod : 1 - ∑ p ∈ Finset.Ico (N + 1) (M + 1), sTerm p
      ≤ ∏ p ∈ Finset.Ico (N + 1) (M + 1), (1 - sTerm p) :=
    one_sub_sum_le_prod_one_sub _ _ (fun i _ => sTerm_nonneg i) (fun i _ => sTerm_le_one i)
  have htail : ∑ p ∈ Finset.Ico (N + 1) (M + 1), sTerm p ≤ 1 / ((N : ℝ) - 1) :=
    tail_sum_le_bound N (M + 1) hN
  have hPN : 0 ≤ partialProduct N := partialProduct_nonneg N
  have hPN1 : partialProduct N ≤ 1 := partialProduct_le_one N
  have hT : 0 ≤ ∑ p ∈ Finset.Ico (N + 1) (M + 1), sTerm p :=
    Finset.sum_nonneg (fun i _ => sTerm_nonneg i)
  rw [partialProduct_split hNM]
  nlinarith

lemma partialProduct_bddBelow : BddBelow (Set.range partialProduct) := by
  refine ⟨0, ?_⟩
  rintro x ⟨N, rfl⟩
  exact partialProduct_nonneg N

/-- The full Euler product `∏_{p odd prime} (1 - 1/(p-1)^2)`, defined as the infimum of the
decreasing sequence of its truncations. -/
noncomputable def eulerProduct : ℝ := ⨅ N : ℕ, partialProduct N

/-- The (twin prime) singular series `𝔖 = 2 ∏_{p odd prime} (1 - 1/(p-1)^2)`. -/
noncomputable def singularSeries : ℝ := 2 * eulerProduct

/-- The truncation of the singular series at `N`. -/
noncomputable def truncatedSingularSeries (N : ℕ) : ℝ := 2 * partialProduct N

lemma eulerProduct_le (N : ℕ) : eulerProduct ≤ partialProduct N :=
  ciInf_le partialProduct_bddBelow N

lemma le_eulerProduct {N : ℕ} (hN : 2 ≤ N) :
    partialProduct N - 1 / ((N : ℝ) - 1) ≤ eulerProduct := by
  refine le_ciInf ?_
  intro M
  rcases le_total N M with h | h
  · exact partialProduct_sub_le hN h
  · have h1 : partialProduct N ≤ partialProduct M := partialProduct_antitone h
    have h2 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have : 0 < 1 / ((N : ℝ) - 1) := by positivity
    linarith

/-- The truncated singular series converges to the singular series. -/
theorem tendsto_truncatedSingularSeries :
    Filter.Tendsto truncatedSingularSeries Filter.atTop (nhds singularSeries) := by
  have h := tendsto_atTop_ciInf partialProduct_antitone partialProduct_bddBelow
  simpa [truncatedSingularSeries, singularSeries, eulerProduct] using h.const_mul (2 : ℝ)

/-- **Effective convergence rate for the singular series.**  For every `N ≥ 2`, the truncation
of the twin-prime singular series at `N` approximates the full singular series with error at
most `2/(N-1)`. -/
theorem SingularSeriesConvergenceRate (N : ℕ) (hN : 2 ≤ N) :
    |truncatedSingularSeries N - singularSeries| ≤ 2 / ((N : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hupper : eulerProduct ≤ partialProduct N := eulerProduct_le N
  have hlower : partialProduct N - 1 / ((N : ℝ) - 1) ≤ eulerProduct := le_eulerProduct hN
  rw [abs_le]
  constructor
  · unfold truncatedSingularSeries singularSeries
    have : (0 : ℝ) < 2 / ((N : ℝ) - 1) := by positivity
    linarith
  · unfold truncatedSingularSeries singularSeries
    have h : 2 / ((N : ℝ) - 1) = 2 * (1 / ((N : ℝ) - 1)) := by ring
    rw [h]
    linarith

/-- The singular series is positive (the argument in fact gives `𝔖 ≥ 5/6`). -/
theorem singularSeries_pos : 0 < singularSeries := by
  have h4 : partialProduct 4 = 3 / 4 := by
    unfold partialProduct sTerm
    norm_num [Finset.prod_range_succ]
  have hlow := le_eulerProduct (N := 4) (by norm_num)
  rw [h4] at hlow
  have : (0 : ℝ) < eulerProduct := by
    norm_num at hlow
    linarith
  unfold singularSeries
  linarith

end Brockian

