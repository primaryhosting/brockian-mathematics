/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is written as an ordinary block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The `p`-th term of the (twin-prime) singular series: `1/(p-1)^2` for odd primes `p`,
and `0` otherwise. -/
noncomputable def singularTerm (n : ℕ) : ℝ :=
  if n.Prime ∧ 2 < n then 1 / ((n : ℝ) - 1) ^ 2 else 0

/-- The `p`-th Euler factor of the (twin-prime) singular series, `1 - 1/(p-1)^2` for odd
primes `p`, and `1` otherwise. -/
noncomputable def singularFactor (n : ℕ) : ℝ := 1 - singularTerm n

/-- The truncated singular series product `∏_{2 < p < N} (1 - 1/(p-1)^2)`. -/
noncomputable def singularPartialProduct (N : ℕ) : ℝ :=
  ∏ p ∈ Finset.range N, singularFactor p

lemma singularTerm_nonneg (n : ℕ) : 0 ≤ singularTerm n := by
  unfold singularTerm
  split
  · positivity
  · exact le_refl 0

lemma singularTerm_le_quarter (n : ℕ) : singularTerm n ≤ 1 / 4 := by
  unfold singularTerm
  split
  · rename_i h
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.2
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  · norm_num

lemma singularFactor_nonneg (n : ℕ) : 0 ≤ singularFactor n := by
  have := singularTerm_le_quarter n
  unfold singularFactor
  linarith

lemma singularFactor_le_one (n : ℕ) : singularFactor n ≤ 1 := by
  have := singularTerm_nonneg n
  unfold singularFactor
  linarith

/-- Telescoping step: for `3 ≤ k`, `singularTerm k ≤ 1/(k-2) - 1/(k-1)`. -/
lemma singularTerm_le_telescope {k : ℕ} (hk : 3 ≤ k) :
    singularTerm k ≤ 1 / ((k : ℝ) - 2) - 1 / ((k : ℝ) - 1) := by
  have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have key : 1 / ((k : ℝ) - 2) - 1 / ((k : ℝ) - 1) = 1 / (((k : ℝ) - 2) * ((k : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  unfold singularTerm
  split
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · positivity

/-- Effective bound on partial sums of the tail of the singular series. -/
lemma sum_range_shift_singularTerm_le {N : ℕ} (hN : 3 ≤ N) (m : ℕ) :
    ∑ i ∈ Finset.range m, singularTerm (i + N)
      ≤ 1 / ((N : ℝ) - 2) - 1 / ((m : ℝ) + (N : ℝ) - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hk : 3 ≤ m + N := by omega
      have h := singularTerm_le_telescope hk
      have hcast : ((m + N : ℕ) : ℝ) = (m : ℝ) + (N : ℝ) := by push_cast; ring
      rw [hcast] at h
      have hcast2 : ((m : ℝ) + 1) + (N : ℝ) - 2 = (m : ℝ) + (N : ℝ) - 1 := by ring
      push_cast
      rw [hcast2]
      linarith

/-- The tail of the singular series over an interval is at most `1/(N-2)`. -/
lemma sum_Ico_singularTerm_le {N M : ℕ} (hN : 3 ≤ N) :
    ∑ p ∈ Finset.Ico N M, singularTerm p ≤ 1 / ((N : ℝ) - 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := sum_range_shift_singularTerm_le hN (M - N)
  have hpos : (0 : ℝ) ≤ 1 / (((M - N : ℕ) : ℝ) + (N : ℝ) - 2) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h4 : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) := Nat.cast_nonneg _
    exact div_nonneg (by norm_num) (by linarith)
  have heq : ∀ k : ℕ, singularTerm (N + k) = singularTerm (k + N) := by
    intro k; rw [Nat.add_comm]
  simp only [heq]
  linarith

/-- **Effective convergence rate for the singular series (sum form).**
The tail `∑_{p ≥ N} 1/(p-1)^2` of the singular series is at most `1/(N-2)`. -/
theorem singularSeries_tail_le {N : ℕ} (hN : 3 ≤ N) :
    ∑' i : ℕ, singularTerm (i + N) ≤ 1 / ((N : ℝ) - 2) := by
  refine Real.tsum_le_of_sum_le (fun i => singularTerm_nonneg _) (fun u => ?_)
  obtain ⟨m, hm⟩ : ∃ m, u ⊆ Finset.range m := ⟨(u.sup id) + 1, by
    intro x hx
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)⟩
  have h1 : ∑ i ∈ u, singularTerm (i + N) ≤ ∑ i ∈ Finset.range m, singularTerm (i + N) :=
    Finset.sum_le_sum_of_subset_of_nonneg hm (fun i _ _ => singularTerm_nonneg _)
  have h2 := sum_range_shift_singularTerm_le hN m
  have hpos : (0 : ℝ) ≤ 1 / ((m : ℝ) + (N : ℝ) - 2) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h4 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    exact div_nonneg (by norm_num) (by linarith)
  linarith

/-- Weierstrass product inequality: `1 - ∑ a ≤ ∏ (1 - a)` for `0 ≤ a i ≤ 1`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      have h0' : ∀ i ∈ s, 0 ≤ a i := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
      have h1' : ∀ i ∈ s, a i ≤ 1 := fun i hi => h1 i (Finset.mem_cons_of_mem hi)
      have hIH := ih h0' h1'
      have hja : 0 ≤ a j := h0 j (Finset.mem_cons_self _ _)
      have hja1 : a j ≤ 1 := h1 j (Finset.mem_cons_self _ _)
      have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg h0'
      nlinarith

lemma singularPartialProduct_nonneg (N : ℕ) : 0 ≤ singularPartialProduct N :=
  Finset.prod_nonneg (fun i _ => singularFactor_nonneg i)

lemma singularPartialProduct_le_one (N : ℕ) : singularPartialProduct N ≤ 1 :=
  Finset.prod_le_one (fun i _ => singularFactor_nonneg i) (fun i _ => singularFactor_le_one i)

lemma singularPartialProduct_split {N M : ℕ} (h : N ≤ M) :
    singularPartialProduct M
      = singularPartialProduct N * ∏ p ∈ Finset.Ico N M, singularFactor p := by
  unfold singularPartialProduct
  simp only [Finset.range_eq_Ico]
  rw [Finset.prod_Ico_consecutive _ (Nat.zero_le N) h]

lemma singularPartialProduct_antitone {N M : ℕ} (h : N ≤ M) :
    singularPartialProduct M ≤ singularPartialProduct N := by
  rw [singularPartialProduct_split h]
  have hq0 : 0 ≤ ∏ p ∈ Finset.Ico N M, singularFactor p :=
    Finset.prod_nonneg (fun i _ => singularFactor_nonneg i)
  have hq1 : ∏ p ∈ Finset.Ico N M, singularFactor p ≤ 1 :=
    Finset.prod_le_one (fun i _ => singularFactor_nonneg i) (fun i _ => singularFactor_le_one i)
  nlinarith [singularPartialProduct_nonneg N, singularPartialProduct_le_one N]

/-- **Singular Series Convergence Rate.**
The truncated singular series products form a Cauchy sequence with the effective rate
`|S_N - S_M| ≤ 1/(N-2)` for all `3 ≤ N ≤ M`; in particular the truncation error of the
singular series at `N` is `O(1/N)`. -/
theorem SingularSeriesConvergenceRate {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    |singularPartialProduct N - singularPartialProduct M| ≤ 1 / ((N : ℝ) - 2) := by
  have hsplit := singularPartialProduct_split hNM
  set Q := ∏ p ∈ Finset.Ico N M, singularFactor p with hQ
  have hq0 : 0 ≤ Q := Finset.prod_nonneg (fun i _ => singularFactor_nonneg i)
  have hq1 : Q ≤ 1 :=
    Finset.prod_le_one (fun i _ => singularFactor_nonneg i) (fun i _ => singularFactor_le_one i)
  have hweier : 1 - ∑ p ∈ Finset.Ico N M, singularTerm p ≤ Q := by
    rw [hQ]
    exact one_sub_sum_le_prod_one_sub _ _ (fun i _ => singularTerm_nonneg i)
      (fun i _ => by have := singularTerm_le_quarter i; linarith)
  have htail := sum_Ico_singularTerm_le (M := M) hN
  have hP0 := singularPartialProduct_nonneg N
  have hP1 := singularPartialProduct_le_one N
  rw [abs_of_nonneg (by nlinarith)]
  rw [hsplit]
  nlinarith

end Brockian

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

