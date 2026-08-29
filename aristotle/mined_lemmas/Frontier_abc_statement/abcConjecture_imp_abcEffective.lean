/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
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

namespace Frontier

/-- The radical `rad n` of a natural number `n`: the product of the distinct primes
dividing `n`.  By convention `rad 0 = rad 1 = 1`. -/

theorem abcConjecture_imp_abcEffective (h : ABCConjecture) : ABCEffective := by
  intro ε hε
  have hfin := (h ε hε).image (fun t => t.2.2)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨(N : ℝ) + 1, ?_⟩
  intro a b c ha hb hab habc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by exact_mod_cast one_le_rad _
  have hrp : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) :=
    Real.one_le_rpow hr1 (by linarith)
  by_cases hex : ((rad (a * b * c) : ℝ)) ^ (1 + ε) < (c : ℝ)
  · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ abcExceptions ε := ⟨ha, hb, hab, habc, hex⟩
    have hcN : (c : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN ⟨_, hmem, rfl⟩
    calc (c:ℝ) ≤ (N:ℝ) + 1 := by linarith
      _ = ((N:ℝ) + 1) * 1 := by ring
      _ ≤ ((N:ℝ) + 1) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith
  · push_neg at hex
    calc (c:ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hex
      _ ≤ ((N:ℝ) + 1) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith

