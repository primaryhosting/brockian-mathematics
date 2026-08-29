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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.OreHarmonicNumbers

open Finset

/-- The number of divisors of `n`, usually written `τ (n)` or `d (n)`. -/

theorem isHarmonic_iff_harmonicMean_nat (n : ℕ) (hn : 0 < n) :
    IsHarmonic n ↔ ∃ k : ℕ, harmonicMean n = k := by
  have hsig : 0 < sigma n := by
    have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
    calc 0 < n := hn
      _ ≤ sigma n := Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) hmem
  have hsig' : (sigma n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsig.ne'
  rw [harmonicMean_eq n]
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    rw [div_eq_iff hsig', ← Nat.cast_mul, ← Nat.cast_mul, hk, mul_comm]
  · rintro ⟨k, hk⟩
    refine ⟨hn, k, ?_⟩
    rw [div_eq_iff hsig'] at hk
    have hcast : ((n * tau n : ℕ) : ℚ) = ((sigma n * k : ℕ) : ℚ) := by
      push_cast; rw [hk]; ring
    exact_mod_cast hcast

/-- **Main result.** There exists an odd Ore harmonic number. -/
