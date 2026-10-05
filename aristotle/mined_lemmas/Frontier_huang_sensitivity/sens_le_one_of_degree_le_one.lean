/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma sens_le_one_of_degree_le_one {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1) :
    sens f ≤ 1 := by
  apply Finset.sup_le
  intro x _
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hab
  have hca := coeff_singleton_ne_zero hdeg ha.2
  have hcb := coeff_singleton_ne_zero hdeg hb.2
  set y := flipAt x b with hy
  have hya : f (flipAt y a) ≠ f y := sensitive_of_coeff hdeg hca y
  have hyb : f (flipAt y b) ≠ f y := sensitive_of_coeff hdeg hcb y
  have e1 := coeff_singleton_mul_sign hdeg ha.2
  have e2 := coeff_singleton_mul_sign hdeg hb.2
  have e3 := coeff_singleton_mul_sign hdeg hya
  have e4 := coeff_singleton_mul_sign hdeg hyb
  have hya' : y a = x a := flipAt_ne x hab
  have hyb' : y b = !x b := flipAt_self x b
  rw [hya'] at e3
  rw [hyb'] at e4
  have hsgn : (if (!x b) then (-1 : ℤ) else 1) = -(if x b then (-1 : ℤ) else 1) := by
    cases x b <;> simp
  rw [hsgn] at e4
  have hgx : (2 : ℤ) ^ n * (if f x then (-1 : ℤ) else 1)
      = 2 ^ n * (if f y then (-1 : ℤ) else 1) := by
    rw [← e1, ← e3]
  have hgy : (2 : ℤ) ^ n * (if f y then (-1 : ℤ) else 1)
      = -(2 ^ n * (if f x then (-1 : ℤ) else 1)) := by
    rw [← e4, ← e2]; ring
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  rw [hgx] at hgy
  cases f y <;> simp at hgy <;> omega

/-- A Boolean function of sensitivity at most one has degree at most one. -/
