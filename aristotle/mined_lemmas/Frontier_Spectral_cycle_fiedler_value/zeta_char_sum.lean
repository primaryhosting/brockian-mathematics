/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma zeta_char_sum {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    ∑ j : Fin n, zeta n ^ (m * (j : ℕ)) = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have key : ∀ j : Fin n, zeta n ^ (m * (j : ℕ)) = (zeta n ^ m) ^ (j : ℕ) := by
    intro j; rw [_root_.zpow_mul, zpow_natCast]
  simp_rw [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => (zeta n ^ m) ^ i)]
  by_cases h : (n : ℤ) ∣ m
  · rw [if_pos h, (zeta_zpow_eq_one_iff hn m).mpr h]; simp
  · rw [if_neg h]
    have hne : zeta n ^ m ≠ 1 := fun hc => h ((zeta_zpow_eq_one_iff hn m).mp hc)
    have hpow : (zeta n ^ m) ^ n = 1 := by
      rw [← zpow_natCast (zeta n ^ m) n, ← _root_.zpow_mul]
      exact (zeta_zpow_eq_one_iff hn _).mpr ⟨m, by ring⟩
    rw [geom_sum_eq hne, hpow]; simp

