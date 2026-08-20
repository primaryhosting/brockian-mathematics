import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem push_real_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (((a : ℝ) + (b : ℝ)) ^ (a + b) / ((a : ℝ) ^ a * (b : ℝ) ^ b)) * (x ^ a * (1 - x) ^ b) ≤ 1 := by
  have hA : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hB : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hM : (0 : ℝ) < (a : ℝ) + (b : ℝ) := by linarith
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith
  set w₁ : ℝ := (a : ℝ) / ((a : ℝ) + (b : ℝ)) with hw1
  set w₂ : ℝ := (b : ℝ) / ((a : ℝ) + (b : ℝ)) with hw2
  have hw1pos : 0 < w₁ := by rw [hw1]; positivity
  have hw2pos : 0 < w₂ := by rw [hw2]; positivity
  have hsum : w₁ + w₂ = 1 := by rw [hw1, hw2, ← add_div, div_self hM.ne']
  set p₁ : ℝ := x * ((a : ℝ) + (b : ℝ)) / (a : ℝ) with hp1
  set p₂ : ℝ := (1 - x) * ((a : ℝ) + (b : ℝ)) / (b : ℝ) with hp2
  have hp1nn : 0 ≤ p₁ := by rw [hp1]; positivity
  have hp2nn : 0 ≤ p₂ := by rw [hp2]; positivity
  have key := Real.geom_mean_le_arith_mean2_weighted hw1pos.le hw2pos.le hp1nn hp2nn hsum
  have harith : w₁ * p₁ + w₂ * p₂ = 1 := by rw [hw1, hw2, hp1, hp2]; field_simp; ring
  rw [harith] at key
  have hu : (0 : ℝ) ≤ p₁ ^ w₁ * p₂ ^ w₂ := by positivity
  have hpow : (p₁ ^ w₁ * p₂ ^ w₂) ^ ((a : ℝ) + (b : ℝ)) ≤ 1 := Real.rpow_le_one hu key hM.le
  have he1 : w₁ * ((a : ℝ) + (b : ℝ)) = (a : ℝ) := by rw [hw1]; field_simp
  have he2 : w₂ * ((a : ℝ) + (b : ℝ)) = (b : ℝ) := by rw [hw2]; field_simp
  have hrw : (p₁ ^ w₁ * p₂ ^ w₂) ^ ((a : ℝ) + (b : ℝ)) = p₁ ^ a * p₂ ^ b := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast p₁ a,
      ← Real.rpow_natCast p₂ b, ← Real.rpow_mul hp1nn, ← Real.rpow_mul hp2nn, he1, he2]
  rw [hrw] at hpow
  have hexp : p₁ ^ a * p₂ ^ b =
      (((a : ℝ) + (b : ℝ)) ^ (a + b) / ((a : ℝ) ^ a * (b : ℝ) ^ b)) * (x ^ a * (1 - x) ^ b) := by
    rw [hp1, hp2, div_pow, div_pow, mul_pow, mul_pow, pow_add]
    field_simp
  rw [hexp] at hpow
  exact hpow

/-- `belyiPush` maps `[0,1]` into `[0,1]` (weighted AM–GM). -/
