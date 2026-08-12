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

set_option grind.warning false

namespace CS

/-- `(b^k)^(log_b a) = a^k`. -/
lemma rpow_natPow_logb (a : ℝ) (b : ℕ) (hb : 2 ≤ b) (ha : 0 < a) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a) = a ^ k := by
  have hb0 : (0:ℝ) < (b:ℝ) := by
    have : (0:ℕ) < b := by omega
    exact_mod_cast this
  have hb1 : (b:ℝ) ≠ 1 := by
    have : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    linarith
  rw [← Real.rpow_natCast (b:ℝ) k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_logb hb0 hb1 ha, Real.rpow_natCast]

/-- `(b^k)^(log_b a - ε) = a^k * (b^(-ε))^k`. -/
lemma rpow_natPow_logb_sub (a : ℝ) (b : ℕ) (eps : ℝ) (hb : 2 ≤ b) (ha : 0 < a) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a - eps) = a ^ k * ((b : ℝ) ^ (-eps)) ^ k := by
  have hb0 : (0:ℝ) < (b:ℝ) := by
    have : (0:ℕ) < b := by omega
    exact_mod_cast this
  have hb1 : (b:ℝ) ≠ 1 := by
    have : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    linarith
  rw [← Real.rpow_natCast (b:ℝ) k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_sub hb0, Real.rpow_logb hb0 hb1 ha, Real.rpow_natCast, ← mul_pow]
  congr 1
  rw [Real.rpow_neg hb0.le, div_eq_mul_inv]

/-- Geometric series bound. -/
lemma geom_sum_le_inv_one_sub (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, r ^ j ≤ (1 - r)⁻¹ := by
  have h1 : r ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq h1]
  have hpos : 0 < 1 - r := by linarith
  have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
  rw [div_le_iff_of_neg (by linarith : r - 1 < 0)]
  have h2 : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have h3 : (1 - r)⁻¹ * (r - 1) = -1 := by linear_combination -h2
  linarith

/-- **Master theorem, case 1.**  Suppose `T` satisfies the divide-and-conquer recurrence
`T n = a * T (n / b) + f n` (formalised along the powers of `b`, where the division is exact),
with `a ≥ 1`, `b ≥ 2`, a nonnegative driving function `f` satisfying
`f n = O (n ^ (log_b a - ε))` for some `ε > 0`, and positive base value `T 1`.
Then `T n = Θ (n ^ (log_b a))` along the powers of `b`: there are positive constants
`c₁, c₂` with `c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`. -/
theorem master_theorem_case1
    (a : ℝ) (b : ℕ) (eps C : ℝ) (f T : ℕ → ℝ)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (heps : 0 < eps) (hC : 0 < C)
    (hfnonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - eps))
    (hT1 : 0 < T 1)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ n : ℕ, (∃ k : ℕ, n = b ^ k) →
      c₁ * (n : ℝ) ^ (Real.logb b a) ≤ T n ∧ T n ≤ c₂ * (n : ℝ) ^ (Real.logb b a) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (1:ℝ) < (b:ℝ) := by
    have : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    linarith
  set r : ℝ := (b:ℝ) ^ (-eps) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg hb0 (by linarith)
  -- Lower bound: unrolling the recurrence and discarding the nonnegative `f`-terms.
  have hlow : ∀ k : ℕ, a ^ k * T 1 ≤ T (b ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hrec k]
      have hf0 := hfnonneg (b ^ (k + 1))
      have h2 : a * (a ^ k * T 1) ≤ a * T (b ^ k) := mul_le_mul_of_nonneg_left ih ha0.le
      calc a ^ (k + 1) * T 1 = a * (a ^ k * T 1) := by ring
        _ ≤ a * T (b ^ k) := h2
        _ ≤ a * T (b ^ k) + f (b ^ (k + 1)) := by linarith
  -- Upper bound: the accumulated `f`-contributions form a geometric series.
  have hup : ∀ k : ℕ, T (b ^ k) ≤ a ^ k * (T 1 + C * ∑ j ∈ Finset.range k, r ^ (j + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hfb : f (b ^ (k + 1)) ≤ C * (a ^ (k + 1) * r ^ (k + 1)) := by
        have h1 : (1:ℕ) ≤ b ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
        have h2 := hf (b ^ (k + 1)) h1
        rwa [Nat.cast_pow, rpow_natPow_logb_sub a b eps hb ha0] at h2
      have h2 : a * T (b ^ k) ≤ a * (a ^ k * (T 1 + C * ∑ j ∈ Finset.range k, r ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left ih ha0.le
      rw [hrec k, Finset.sum_range_succ]
      have h3 : a ^ (k + 1) * (T 1 + C * ((∑ j ∈ Finset.range k, r ^ (j + 1)) + r ^ (k + 1)))
          = a * (a ^ k * (T 1 + C * ∑ j ∈ Finset.range k, r ^ (j + 1)))
            + C * (a ^ (k + 1) * r ^ (k + 1)) := by ring
      rw [h3]
      linarith
  have hinv : 0 < (1 - r)⁻¹ := inv_pos.mpr (by linarith)
  refine ⟨T 1, T 1 + C * (1 - r)⁻¹, hT1, by nlinarith, ?_⟩
  rintro n ⟨k, rfl⟩
  rw [Nat.cast_pow]
  refine ⟨?_, ?_⟩
  · rw [rpow_natPow_logb a b hb ha0 k, mul_comm]
    exact hlow k
  · rw [rpow_natPow_logb a b hb ha0 k]
    have hsum : (∑ j ∈ Finset.range k, r ^ (j + 1)) ≤ (1 - r)⁻¹ := by
      have h1 : (∑ j ∈ Finset.range k, r ^ (j + 1)) = r * ∑ j ∈ Finset.range k, r ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have h2 := geom_sum_le_inv_one_sub r hr0.le hr1 k
      have h3 : 0 ≤ ∑ j ∈ Finset.range k, r ^ j :=
        Finset.sum_nonneg (fun j _ => pow_nonneg hr0.le j)
      nlinarith
    have hak : (0:ℝ) ≤ a ^ k := pow_nonneg ha0.le k
    have key : a ^ k * (C * ∑ j ∈ Finset.range k, r ^ (j + 1)) ≤ a ^ k * (C * (1 - r)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hC.le) hak
    calc T (b ^ k) ≤ a ^ k * (T 1 + C * ∑ j ∈ Finset.range k, r ^ (j + 1)) := hup k
      _ ≤ (T 1 + C * (1 - r)⁻¹) * a ^ k := by nlinarith [key]

/-- Two-sided bounds by a positive function give a `Θ`-estimate. -/
lemma isTheta_of_two_sided_bounds (S g : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hg : ∀ k, 0 < g k) (h : ∀ k, c₁ * g k ≤ S k ∧ S k ≤ c₂ * g k) :
    S =Θ[Filter.atTop] g := by
  constructor
  · refine Asymptotics.IsBigO.of_bound c₂ (Filter.Eventually.of_forall fun k => ?_)
    have h1 := (h k).1
    have h2 := (h k).2
    have hgk := hg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ S k),
      abs_of_nonneg hgk.le]
    exact h2
  · refine Asymptotics.IsBigO.of_bound c₁⁻¹ (Filter.Eventually.of_forall fun k => ?_)
    have h1 := (h k).1
    have hgk := hg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ S k),
      abs_of_nonneg hgk.le]
    have h2 : c₁⁻¹ * (c₁ * g k) ≤ c₁⁻¹ * S k :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc₁.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hc₁.ne', one_mul] at h2

/-- **Master theorem, case 1**, stated as a genuine `Θ`-asymptotic along the powers of `b`:
under the hypotheses of `CS.master_theorem_case1`, the map `k ↦ T (b ^ k)` is `Θ` of
`k ↦ (b ^ k) ^ (log_b a)` as `k → ∞`. -/
theorem master_theorem_case1_isTheta
    (a : ℝ) (b : ℕ) (eps C : ℝ) (f T : ℕ → ℝ)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (heps : 0 < eps) (hC : 0 < C)
    (hfnonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - eps))
    (hT1 : 0 < T 1)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) :
    (fun k : ℕ => T (b ^ k)) =Θ[Filter.atTop]
      (fun k : ℕ => ((b : ℝ) ^ k) ^ (Real.logb b a)) := by
  obtain ⟨c₁, c₂, hc₁, _hc₂, h⟩ :=
    master_theorem_case1 a b eps C f T ha hb heps hC hfnonneg hf hT1 hrec
  have hb0 : (0:ℝ) < (b:ℝ) := by
    have : (0:ℕ) < b := by omega
    exact_mod_cast this
  refine isTheta_of_two_sided_bounds _ _ c₁ c₂ hc₁
    (fun k => Real.rpow_pos_of_pos (pow_pos hb0 k) _) (fun k => ?_)
  have := h (b ^ k) ⟨k, rfl⟩
  rwa [Nat.cast_pow] at this

end CS

