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

