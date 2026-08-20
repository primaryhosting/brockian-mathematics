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

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

lemma summable_log_sq_div_sq :
    Summable (fun N : ℕ => ((Nat.log 2 N : ℝ) + 1) ^ 2 / N ^ 2) := by
  obtain ⟨N₀, hN₀⟩ := exists_log_poly_bound 1 4
  set n₀ := max N₀ 1 with hn₀
  have hg : Summable (fun n : ℕ => 1 / ((n:ℝ) * Real.sqrt n)) := by
    have h : Summable (fun n : ℕ => 1 / (n:ℝ) ^ ((3:ℝ)/2)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    refine h.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn' : (0:ℝ) < n := by exact_mod_cast hn
      rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hn', Real.rpow_one,
        ← Real.sqrt_eq_rpow]
  rw [← summable_nat_add_iff n₀]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff n₀).mpr hg)
  set N := n + n₀ with hN
  have hN1 : 1 ≤ N := by omega
  have hNn : N₀ ≤ N := by omega
  have hL4 : (Nat.log 2 N + 1) ^ 4 ≤ N := by simpa using hN₀ N hNn
  have hn' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  set L := ((Nat.log 2 N : ℝ) + 1) with hLdef
  have hL4' : L ^ 4 ≤ (N:ℝ) := by
    have hcast : (((Nat.log 2 N + 1) ^ 4 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hL4
    push_cast at hcast
    linarith
  have hsqrt : L ^ 2 ≤ Real.sqrt N := by
    rw [show L ^ 2 = Real.sqrt (L ^ 4) by
      rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hL4'
  have hsq : Real.sqrt N * Real.sqrt N = (N:ℝ) := Real.mul_self_sqrt hn'.le
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn'
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc L ^ 2 * ((N:ℝ) * Real.sqrt N) ≤ Real.sqrt N * ((N:ℝ) * Real.sqrt N) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = 1 * (N:ℝ) ^ 2 := by rw [one_mul]; nlinarith [hsq]

/-- The dyadic block sums `twinCount (2^(N+1)) / 2^N` are summable. -/
