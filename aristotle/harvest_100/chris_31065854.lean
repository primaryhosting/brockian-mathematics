/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-- `((b:ℝ)^k) ^ (log_b a + t) = a^k * (b^t)^k` (real powers).
Specializing `t = 0` gives `(b^k)^{log_b a} = a^k`, i.e. `n^{log_b a} = a^k` for `n = b^k`. -/
private lemma rpow_pow_logb_add (a : ℝ) (b : ℕ) (ha : 0 < a) (hb : 2 ≤ b) (k : ℕ) (t : ℝ) :
    (((b : ℝ) ^ k)) ^ (Real.logb b a + t) = a ^ k * (((b : ℝ) ^ t) ^ k) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hbl : (b : ℝ) ^ (Real.logb b a) = a := Real.rpow_logb hb0 (by linarith) ha
  rw [← Real.rpow_natCast (b : ℝ) k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_natCast, Real.rpow_add hb0, hbl, mul_pow]

/-- Partial sums of a geometric series with ratio in `[0,1)` are bounded by `(1-r)⁻¹`. -/
private lemma geom_partial_sum_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, r ^ i ≤ (1 - r)⁻¹ := by
  have hm := geom_sum_mul r k
  have hk : (0 : ℝ) ≤ r ^ k := pow_nonneg h0 k
  rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
  nlinarith

/--
**Master theorem, Case 1.**

Let `T (n) = a * T (n / b) + f (n)` be a divide-and-conquer recurrence, considered (as usual)
along the exact powers `n = b ^ k` of the branching factor `b ≥ 2`, with `a ≥ 1` subproblems.
If the combine cost satisfies `f (n) = O (n ^ (log_b a - ε))` for some `ε > 0`
(here with explicit constant `C`), and `f ≥ 0`, `T 1 > 0`, then

  `T (n) = Θ (n ^ (log_b a))`,

i.e. there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`.
-/
theorem master_theorem_case1
    (a : ℝ) (b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (eps C : ℝ) (heps : 0 < eps) (hC : 0 < C)
    (T f : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - eps))
    (hT1 : 0 < T 1)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b ^ k : ℕ) : ℝ) ^ (Real.logb b a) ≤ T (b ^ k) ∧
        T (b ^ k) ≤ c₂ * ((b ^ k : ℕ) : ℝ) ^ (Real.logb b a) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  set r : ℝ := (b : ℝ) ^ (-eps) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos hb0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb1 (by linarith)
  -- `n ^ (log_b a) = a ^ k` for `n = b ^ k`
  have hcast : ∀ k : ℕ, ((b ^ k : ℕ) : ℝ) = ((b : ℝ)) ^ k := by
    intro k; push_cast; ring
  have hpow : ∀ k : ℕ, ((b ^ k : ℕ) : ℝ) ^ (Real.logb b a) = a ^ k := by
    intro k
    rw [hcast k]
    have := rpow_pow_logb_add a b ha0 hb k 0
    simpa using this
  -- `n ^ (log_b a - ε) = a ^ k * r ^ k` for `n = b ^ k`
  have hpow' : ∀ k : ℕ, ((b ^ k : ℕ) : ℝ) ^ (Real.logb b a - eps) = a ^ k * r ^ k := by
    intro k
    rw [hcast k, sub_eq_add_neg]
    exact rpow_pow_logb_add a b ha0 hb k (-eps)
  -- lower bound
  have hlow : ∀ k : ℕ, T 1 * a ^ k ≤ T (b ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [hrec k]
        have h1 : a * (T 1 * a ^ k) ≤ a * T (b ^ k) := by
          exact mul_le_mul_of_nonneg_left ih ha0.le
        have h2 := hf0 (b ^ (k + 1))
        calc T 1 * a ^ (k + 1) = a * (T 1 * a ^ k) := by ring
          _ ≤ a * T (b ^ k) := h1
          _ ≤ a * T (b ^ k) + f (b ^ (k + 1)) := by linarith
  -- upper bound, with a strengthened induction hypothesis
  have hup : ∀ k : ℕ, T (b ^ k) ≤ a ^ k * (T 1 + C * ∑ i ∈ Finset.range k, r ^ (i + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hbk1 : 1 ≤ b ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
        have hfb : f (b ^ (k + 1)) ≤ C * (a ^ (k + 1) * r ^ (k + 1)) := by
          have := hf (b ^ (k + 1)) hbk1
          rwa [hpow' (k + 1)] at this
        have h1 : a * T (b ^ k) ≤ a * (a ^ k * (T 1 + C * ∑ i ∈ Finset.range k, r ^ (i + 1))) :=
          mul_le_mul_of_nonneg_left ih ha0.le
        rw [hrec k, Finset.sum_range_succ]
        calc a * T (b ^ k) + f (b ^ (k + 1))
            ≤ a * (a ^ k * (T 1 + C * ∑ i ∈ Finset.range k, r ^ (i + 1)))
                + C * (a ^ (k + 1) * r ^ (k + 1)) := by linarith
          _ = a ^ (k + 1) * (T 1 + C * ((∑ i ∈ Finset.range k, r ^ (i + 1)) + r ^ (k + 1))) := by
                ring
  -- the geometric tail is bounded uniformly in `k`
  have hgeom : ∀ k : ℕ, (∑ i ∈ Finset.range k, r ^ (i + 1)) ≤ (1 - r)⁻¹ := by
    intro k
    have h1 : (∑ i ∈ Finset.range k, r ^ (i + 1)) = r * ∑ i ∈ Finset.range k, r ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have h2 := geom_partial_sum_le r hr0.le hr1 k
    have h3 : (0 : ℝ) < (1 - r)⁻¹ := inv_pos.mpr (by linarith)
    rw [h1]
    nlinarith
  refine ⟨T 1, T 1 + C * (1 - r)⁻¹, hT1, ?_, ?_⟩
  · have : (0 : ℝ) < C * (1 - r)⁻¹ := mul_pos hC (inv_pos.mpr (by linarith))
    linarith
  · intro k
    have hak : (0 : ℝ) < a ^ k := pow_pos ha0 k
    constructor
    · rw [hpow k]; exact hlow k
    · rw [hpow k]
      have h1 := hup k
      have h2 : C * ∑ i ∈ Finset.range k, r ^ (i + 1) ≤ C * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left (hgeom k) hC.le
      have h3 : a ^ k * (T 1 + C * ∑ i ∈ Finset.range k, r ^ (i + 1))
          ≤ a ^ k * (T 1 + C * (1 - r)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hak.le
        linarith
      calc T (b ^ k) ≤ a ^ k * (T 1 + C * ∑ i ∈ Finset.range k, r ^ (i + 1)) := h1
        _ ≤ a ^ k * (T 1 + C * (1 - r)⁻¹) := h3
        _ = (T 1 + C * (1 - r)⁻¹) * a ^ k := by ring

/-- Sanity check that the hypotheses of `master_theorem_case1` are satisfiable
(so the theorem is not vacuous): `T n = n`, `f = 0`, `a = b = 2`, `ε = C = 1`. -/
example : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
    c₁ * ((2 ^ k : ℕ) : ℝ) ^ (Real.logb 2 2) ≤ ((2 ^ k : ℕ) : ℝ) ∧
      ((2 ^ k : ℕ) : ℝ) ≤ c₂ * ((2 ^ k : ℕ) : ℝ) ^ (Real.logb 2 2) := by
  have h := master_theorem_case1 2 2 (by norm_num) (by norm_num) 1 1 (by norm_num) (by norm_num)
    (fun n => (n : ℝ)) (fun _ => 0) (fun _ => le_rfl)
    (fun n _ => by simp)
    (by norm_num)
    (fun k => by push_cast [pow_succ]; ring)
  simpa using h

end CS

