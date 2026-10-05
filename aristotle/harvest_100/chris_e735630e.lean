/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-- The divide-and-conquer recurrence `T(n) = a * T(n / b) + f(n)`, sampled along the
exact powers `n = b ^ k` of the branching factor.  `masterT a f T₀ k` is the value of
`T` at `n = b ^ k`, and `f k` stands for the driving cost `f (b ^ k)`. -/
noncomputable def masterT (a : ℝ) (f : ℕ → ℝ) (T₀ : ℝ) : ℕ → ℝ
  | 0 => T₀
  | (k + 1) => a * masterT a f T₀ k + f (k + 1)

section

variable {a b : ℝ}

/-- `(b ^ k) ^ (log_b a) = a ^ k`. -/
theorem rpow_logb_pow (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a) = a ^ k := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_logb hb0 (ne_of_gt hb) ha, Real.rpow_natCast]

/-- `(b ^ k) ^ (log_b a - ε) = a ^ k * (b ^ (-ε)) ^ k`. -/
theorem rpow_logb_sub_pow (ha : 0 < a) (hb : 1 < b) (eps : ℝ) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a - eps) = a ^ k * ((b : ℝ) ^ (-eps)) ^ k := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  have hbk : (0:ℝ) < (b : ℝ) ^ k := pow_pos hb0 k
  rw [Real.rpow_sub hbk, rpow_logb_pow ha hb k]
  have h2 : ((b : ℝ) ^ k) ^ eps = ((b : ℝ) ^ eps) ^ k := by
    rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
      Real.rpow_natCast]
  have h3 : ((b : ℝ) ^ (-eps)) ^ k = (((b : ℝ) ^ eps) ^ k)⁻¹ := by
    rw [Real.rpow_neg hb0.le, ← inv_pow]
  rw [h2, h3, div_eq_mul_inv]

end

/-- **Master theorem, case 1.**

If `T(b^k) = a * T(b^(k-1)) + f(b^k)` with `a > 0`, `b > 1`, a positive base value `T₀`,
a nonnegative driving term `f` satisfying `f(n) = O(n ^ (log_b a - ε))` for some `ε > 0`
(here in the explicit form `f (b^k) ≤ C * (b^k) ^ (log_b a - ε)`), then
`T(n) = Θ(n ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T(n) ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`. -/
theorem master_theorem_case1
    (a b eps C T₀ : ℝ) (f : ℕ → ℝ)
    (ha : 0 < a) (hb : 1 < b) (heps : 0 < eps) (hC : 0 ≤ C) (hT₀ : 0 < T₀)
    (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ C * ((b : ℝ) ^ k) ^ (Real.logb b a - eps)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * (((b : ℝ) ^ k) ^ (Real.logb b a)) ≤ masterT a f T₀ k ∧
        masterT a f T₀ k ≤ c₂ * (((b : ℝ) ^ k) ^ (Real.logb b a)) := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  set d : ℝ := (b : ℝ) ^ (-eps) with hd_def
  have hd0 : 0 < d := Real.rpow_pos_of_pos hb0 _
  have hd1 : d < 1 := by
    rw [hd_def]
    exact Real.rpow_lt_one_of_one_lt_of_neg hb (neg_neg_iff_pos.mpr heps)
  -- the constant `C * (1 / (1 - d))` absorbs the geometric series
  set M : ℝ := T₀ + C * (1 / (1 - d)) with hM_def
  have h1d : 0 < 1 - d := by linarith
  have hMpos : 0 < M := by
    have : 0 ≤ C * (1 / (1 - d)) := mul_nonneg hC (by positivity)
    linarith
  -- geometric sum bound
  have hgeom : ∀ k : ℕ, (∑ j ∈ Finset.range k, d ^ (j + 1)) ≤ 1 / (1 - d) := by
    intro k
    have hsum : (∑ j ∈ Finset.range k, d ^ (j + 1)) ≤ ∑ j ∈ Finset.range k, d ^ j := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact pow_le_pow_of_le_one hd0.le hd1.le (Nat.le_succ j)
    have key : (∑ j ∈ Finset.range k, d ^ j) * (1 - d) = 1 - d ^ k := by
      linear_combination -(geom_sum_mul d k)
    have h2 : (∑ j ∈ Finset.range k, d ^ j) ≤ 1 / (1 - d) := by
      rw [le_div_iff₀ h1d, key]
      nlinarith [pow_nonneg hd0.le k]
    linarith
  refine ⟨T₀, M, hT₀, hMpos, ?_⟩
  intro k
  constructor
  · -- lower bound
    have hlow : ∀ k : ℕ, T₀ * a ^ k ≤ masterT a f T₀ k := by
      intro k
      induction k with
      | zero => simp [masterT]
      | succ n ih =>
        have := hf0 (n + 1)
        have h : a * (T₀ * a ^ n) ≤ a * masterT a f T₀ n :=
          mul_le_mul_of_nonneg_left ih ha.le
        have hp : T₀ * a ^ (n + 1) = a * (T₀ * a ^ n) := by ring
        simp only [masterT]
        linarith
    rw [rpow_logb_pow ha hb k]
    exact hlow k
  · -- upper bound
    have hup : ∀ k : ℕ, masterT a f T₀ k ≤
        a ^ k * (T₀ + C * ∑ j ∈ Finset.range k, d ^ (j + 1)) := by
      intro k
      induction k with
      | zero => simp [masterT]
      | succ n ih =>
        have hfn : f (n + 1) ≤ C * (a ^ (n + 1) * d ^ (n + 1)) := by
          have := hf (n + 1)
          rwa [rpow_logb_sub_pow ha hb eps (n + 1)] at this
        have h : a * masterT a f T₀ n ≤
            a * (a ^ n * (T₀ + C * ∑ j ∈ Finset.range n, d ^ (j + 1))) :=
          mul_le_mul_of_nonneg_left ih ha.le
        have hexp : a ^ (n + 1) *
              (T₀ + C * ((∑ j ∈ Finset.range n, d ^ (j + 1)) + d ^ (n + 1))) =
            a * (a ^ n * (T₀ + C * ∑ j ∈ Finset.range n, d ^ (j + 1))) +
              C * (a ^ (n + 1) * d ^ (n + 1)) := by ring
        simp only [masterT, Finset.sum_range_succ]
        linarith
    have := hup k
    rw [rpow_logb_pow ha hb k]
    have hb2 : C * ∑ j ∈ Finset.range k, d ^ (j + 1) ≤ C * (1 / (1 - d)) :=
      mul_le_mul_of_nonneg_left (hgeom k) hC
    have hak : (0:ℝ) < a ^ k := pow_pos ha k
    calc masterT a f T₀ k ≤ a ^ k * (T₀ + C * ∑ j ∈ Finset.range k, d ^ (j + 1)) := this
      _ ≤ a ^ k * M := by
          apply mul_le_mul_of_nonneg_left _ hak.le
          rw [hM_def]; linarith
      _ = M * a ^ k := by ring

/-- **Master theorem, case 1, asymptotic form.**

Under the hypotheses of `CS.master_theorem_case1`, the solution of the recurrence really is
`Θ (n ^ (log_b a))` in the sense of `Asymptotics.IsTheta`, along `n = b ^ k` with `k → ∞`. -/
theorem master_theorem_case1_isTheta
    (a b eps C T₀ : ℝ) (f : ℕ → ℝ)
    (ha : 0 < a) (hb : 1 < b) (heps : 0 < eps) (hC : 0 ≤ C) (hT₀ : 0 < T₀)
    (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ C * ((b : ℝ) ^ k) ^ (Real.logb b a - eps)) :
    (fun k : ℕ => masterT a f T₀ k) =Θ[Filter.atTop]
      (fun k : ℕ => ((b : ℝ) ^ k) ^ (Real.logb b a)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hbounds⟩ :=
    master_theorem_case1 a b eps C T₀ f ha hb heps hC hT₀ hf0 hf
  have hgpos : ∀ k : ℕ, 0 < ((b : ℝ) ^ k) ^ (Real.logb b a) := by
    intro k
    rw [rpow_logb_pow ha hb k]
    exact pow_pos ha k
  have hTpos : ∀ k : ℕ, 0 < masterT a f T₀ k := fun k =>
    lt_of_lt_of_le (mul_pos hc₁ (hgpos k)) (hbounds k).1
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨c₂, Filter.Eventually.of_forall fun k => ?_⟩
    rw [Real.norm_of_nonneg (hTpos k).le, Real.norm_of_nonneg (hgpos k).le]
    exact (hbounds k).2
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1 / c₁, Filter.Eventually.of_forall fun k => ?_⟩
    rw [Real.norm_of_nonneg (hTpos k).le, Real.norm_of_nonneg (hgpos k).le]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc₁, mul_comm]
    exact (hbounds k).1

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

