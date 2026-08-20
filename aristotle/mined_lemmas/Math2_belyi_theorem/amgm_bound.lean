import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma amgm_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x ^ m * (1 - x) ^ n * ((m : ℝ) + n) ^ (m + n) ≤ (m : ℝ) ^ m * (n : ℝ) ^ n := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set s : ℝ := (m:ℝ) + n with hsdef
  have hs : (0:ℝ) < s := by positivity
  have hx1 : (0:ℝ) ≤ 1 - x := by linarith
  have hp1 : (0:ℝ) ≤ x * s / m := by positivity
  have hp2 : (0:ℝ) ≤ (1 - x) * s / n := by positivity
  have hw : (m:ℝ)/s + (n:ℝ)/s = 1 := by rw [← add_div, hsdef]; field_simp
  have key := Real.geom_mean_le_arith_mean2_weighted (by positivity : (0:ℝ) ≤ (m:ℝ)/s)
    (by positivity : (0:ℝ) ≤ (n:ℝ)/s) hp1 hp2 hw
  have hrhs : ((m:ℝ)/s) * (x * s / m) + ((n:ℝ)/s) * ((1-x) * s / n) = 1 := by
    field_simp
    ring
  rw [hrhs] at key
  have h2 : ((x * s / m) ^ ((m:ℝ)/s) * ((1-x) * s / n) ^ ((n:ℝ)/s)) ^ s ≤ (1:ℝ) ^ s :=
    Real.rpow_le_rpow (by positivity) key (le_of_lt hs)
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hp1, ← Real.rpow_mul hp2,
    div_mul_cancel₀ _ (ne_of_gt hs), div_mul_cancel₀ _ (ne_of_gt hs), Real.one_rpow,
    Real.rpow_natCast, Real.rpow_natCast] at h2
  rw [div_pow, div_pow, mul_pow, mul_pow, div_mul_div_comm, div_le_one (by positivity)] at h2
  rw [pow_add]
  calc x ^ m * (1 - x) ^ n * (s ^ m * s ^ n) = x ^ m * s ^ m * ((1 - x) ^ n * s ^ n) := by ring
    _ ≤ (m:ℝ) ^ m * (n:ℝ) ^ n := h2

/-- The Belyi polynomial maps `[0,1]` into `[0,1]`. -/
