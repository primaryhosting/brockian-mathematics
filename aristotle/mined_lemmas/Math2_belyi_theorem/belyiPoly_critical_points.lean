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

lemma belyiPoly_critical_points (a b : ℕ) {c : ℂ}
    (h : aeval c (derivative (belyiPoly a b)) = 0) :
    c = 0 ∨ c = 1 ∨ c = algebraMap ℚ ℂ (belyiCrit a b) := by
  rw [belyiPoly_derivative] at h
  simp only [map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one, map_add, map_ofNat,
    map_natCast, mul_eq_zero] at h
  have hbc : (algebraMap ℚ ℂ) (belyiConst a b) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).2 (belyiConst_ne_zero a b)
  have hden : ((a:ℚ) + b + 2) ≠ 0 := by positivity
  have hneQ : ((a : ℂ) + (b : ℂ) + 2) ≠ 0 := by
    rw [show ((a : ℂ) + (b : ℂ) + 2) = algebraMap ℚ ℂ ((a:ℚ) + b + 2) by
      simp only [map_add, map_natCast, map_ofNat]]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).2 hden
  rcases h with h | h | h | h
  · exact absurd h hbc
  · exact Or.inl (pow_eq_zero_iff'.1 h).1
  · refine Or.inr (Or.inl ?_)
    have h1 : (1 : ℂ) - c = 0 := (pow_eq_zero_iff'.1 h).1
    linear_combination -h1
  · refine Or.inr (Or.inr ?_)
    rw [belyiCrit, map_div₀]
    simp only [map_add, map_natCast, map_ofNat, map_one]
    rw [eq_div_iff hneQ]
    linear_combination -h

/-- Evaluating at a rational point commutes with the embedding `ℚ → ℚ̄`. -/
