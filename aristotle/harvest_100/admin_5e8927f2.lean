import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- For `b > 0`, taking the `k`-th (natural) power commutes with the real power `c`. -/
lemma pow_rpow_comm {b : ℝ} (hb : 0 < b) (c : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ c = (b ^ c) ^ k := by
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb.le, mul_comm, Real.rpow_mul hb.le,
    Real.rpow_natCast]

/-- `(b^k)^(log_b a) = a^k`. -/
lemma pow_rpow_logb {a b : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  rw [pow_rpow_comm (lt_trans zero_lt_one hb), Real.rpow_logb (lt_trans zero_lt_one hb)
    (ne_of_gt hb) ha]

/-- The geometric sum bound `∑_{j<n} q^j ≤ (1-q)⁻¹` for `0 ≤ q < 1`. -/
lemma geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ := by
  have h1 : (0:ℝ) < 1 - q := by linarith
  rw [geom_sum_eq (by linarith : q ≠ 1)]
  rw [div_le_iff_of_neg (by linarith : q - 1 < 0)]
  have : (0:ℝ) ≤ q ^ n := pow_nonneg hq0 n
  have h2 : (1 - q)⁻¹ * (q - 1) = -1 := by
    field_simp
    ring
  rw [h2]
  linarith

/-- **Master theorem, Case 1.**

Let `T` satisfy the divide-and-conquer recurrence `T(b^(k+1)) = a * T(b^k) + f(b^(k+1))`
(here `T k` and `f k` denote the values at `n = b^k`), with `a > 0`, `b > 1`, and
`f(n) = O(n^(log_b a - ε))` for some `ε > 0`.  Then `T(n) = Θ(n^(log_b a))`. -/
theorem master_theorem_case1
    {a b eps C : ℝ} (ha : 0 < a) (hb : 1 < b) (heps : 0 < eps) (hC : 0 ≤ C)
    {f T : ℕ → ℝ} (hfnonneg : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ C * ((b ^ k : ℝ)) ^ (Real.logb b a - eps))
    (hT0 : 0 < T 0)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b ^ k : ℝ)) ^ (Real.logb b a) ≤ T k ∧
        T k ≤ c₂ * ((b ^ k : ℝ)) ^ (Real.logb b a) := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  set q : ℝ := b ^ (-eps) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hb0 _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  -- rewrite the bound on `f`
  have hfb : ∀ k : ℕ, f k ≤ C * (a ^ k * q ^ k) := by
    intro k
    refine le_trans (hf k) ?_
    have : ((b ^ k : ℝ)) ^ (Real.logb b a - eps)
        = ((b ^ k : ℝ)) ^ (Real.logb b a) * ((b ^ k : ℝ)) ^ (-eps) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    rw [this, pow_rpow_logb ha hb, pow_rpow_comm hb0]
  -- lower bound
  have hlow : ∀ k : ℕ, T 0 * a ^ k ≤ T k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have := hfnonneg (k + 1)
        have hkey : a * (T 0 * a ^ k) ≤ a * T k := by
          exact mul_le_mul_of_nonneg_left ih ha.le
        rw [hrec k, pow_succ]
        nlinarith
  -- upper bound via partial geometric sums
  have hup : ∀ k : ℕ, T k ≤ a ^ k * (T 0 + C * ∑ j ∈ Finset.range (k + 1), q ^ j) := by
    intro k
    induction k with
    | zero =>
        have : (0:ℝ) ≤ C * ∑ j ∈ Finset.range 1, q ^ j := by
          apply mul_nonneg hC
          exact Finset.sum_nonneg fun j _ => pow_nonneg hq0.le j
        simpa using by linarith
    | succ k ih =>
        have h1 : a * T k ≤ a * (a ^ k * (T 0 + C * ∑ j ∈ Finset.range (k + 1), q ^ j)) :=
          mul_le_mul_of_nonneg_left ih ha.le
        have h2 : f (k + 1) ≤ C * (a ^ (k + 1) * q ^ (k + 1)) := hfb (k + 1)
        rw [hrec k]
        have hsum : ∑ j ∈ Finset.range (k + 2), q ^ j
            = (∑ j ∈ Finset.range (k + 1), q ^ j) + q ^ (k + 1) := by
          rw [Finset.sum_range_succ]
        rw [hsum, pow_succ]
        rw [pow_succ] at h2
        linarith
  refine ⟨T 0, T 0 + C * (1 - q)⁻¹, hT0, ?_, ?_⟩
  · have : (0:ℝ) ≤ C * (1 - q)⁻¹ := by
      apply mul_nonneg hC
      simp only [inv_nonneg]
      linarith
    linarith
  · intro k
    rw [pow_rpow_logb ha hb]
    refine ⟨by simpa [mul_comm] using hlow k, ?_⟩
    refine le_trans (hup k) ?_
    have hs : (∑ j ∈ Finset.range (k + 1), q ^ j) ≤ (1 - q)⁻¹ :=
      geom_sum_le_inv_one_sub hq0.le hq1 (k + 1)
    have hak : (0:ℝ) < a ^ k := pow_pos ha k
    have : T 0 + C * ∑ j ∈ Finset.range (k + 1), q ^ j ≤ T 0 + C * (1 - q)⁻¹ := by
      nlinarith
    calc a ^ k * (T 0 + C * ∑ j ∈ Finset.range (k + 1), q ^ j)
        ≤ a ^ k * (T 0 + C * (1 - q)⁻¹) := by nlinarith
      _ = (T 0 + C * (1 - q)⁻¹) * a ^ k := by ring

open Asymptotics Filter in
/-- A nonnegative sequence which is `O(g)` along `atTop`, with `g` everywhere positive,
satisfies a *global* bound `f k ≤ C * g k` for all `k`. -/
lemma exists_global_bound_of_isBigO {f g : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 < g k)
    (h : f =O[atTop] g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, f k ≤ C * g k := by
  obtain ⟨C, hC⟩ := h.bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  obtain ⟨M, hM⟩ := ((Finset.range N).image (fun k => f k / g k)).exists_le
  refine ⟨max (max C M) 0, le_max_right _ _, fun k => ?_⟩
  have hgk : 0 < g k := hg k
  have hmax1 : C ≤ max (max C M) 0 := le_trans (le_max_left C M) (le_max_left _ _)
  have hmax2 : M ≤ max (max C M) 0 := le_trans (le_max_right C M) (le_max_left _ _)
  by_cases hk : N ≤ k
  · have hb := hN k hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf k), abs_of_nonneg hgk.le] at hb
    nlinarith
  · have hmem : f k / g k ≤ M :=
      hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))
    rw [div_le_iff₀ hgk] at hmem
    nlinarith

open Asymptotics Filter in
/-- **Master theorem, Case 1**, stated with Mathlib's asymptotic notation.

If `T` satisfies `T(b^(k+1)) = a * T(b^k) + f(b^(k+1))` with `a > 0`, `b > 1`, `f ≥ 0` and
`f(n) = O(n^(log_b a - ε))` for some `ε > 0`, then `T(n) = Θ(n^(log_b a))`
(along `n = b^k`, `k → ∞`). -/
theorem master_theorem_case1_isTheta
    {a b eps : ℝ} (ha : 0 < a) (hb : 1 < b) (heps : 0 < eps)
    {f T : ℕ → ℝ} (hfnonneg : ∀ k, 0 ≤ f k)
    (hf : f =O[atTop] fun k : ℕ => ((b ^ k : ℝ)) ^ (Real.logb b a - eps))
    (hT0 : 0 < T 0)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1)) :
    T =Θ[atTop] fun k : ℕ => ((b ^ k : ℝ)) ^ (Real.logb b a) := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  have hgpos : ∀ k : ℕ, (0:ℝ) < ((b ^ k : ℝ)) ^ (Real.logb b a - eps) :=
    fun k => Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨C, hC, hCb⟩ := exists_global_bound_of_isBigO hfnonneg hgpos hf
  obtain ⟨c₁, c₂, hc₁, hc₂, hbounds⟩ :=
    master_theorem_case1 ha hb heps hC hfnonneg hCb hT0 hrec
  have hGpos : ∀ k : ℕ, (0:ℝ) < ((b ^ k : ℝ)) ^ (Real.logb b a) :=
    fun k => Real.rpow_pos_of_pos (by positivity) _
  constructor
  · refine IsBigO.of_bound c₂ (Filter.Eventually.of_forall fun k => ?_)
    have h1 := (hbounds k).1
    have h2 := (hbounds k).2
    have hT : 0 < T k := lt_of_lt_of_le (mul_pos hc₁ (hGpos k)) h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT.le, abs_of_nonneg (hGpos k).le]
    exact h2
  · refine IsBigO.of_bound c₁⁻¹ (Filter.Eventually.of_forall fun k => ?_)
    have h1 := (hbounds k).1
    have hT : 0 < T k := lt_of_lt_of_le (mul_pos hc₁ (hGpos k)) h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT.le, abs_of_nonneg (hGpos k).le]
    calc ((b ^ k : ℝ)) ^ (Real.logb b a)
        = c₁⁻¹ * (c₁ * ((b ^ k : ℝ)) ^ (Real.logb b a)) := by
          field_simp
      _ ≤ c₁⁻¹ * T k := mul_le_mul_of_nonneg_left h1 (by positivity)

end CS

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

