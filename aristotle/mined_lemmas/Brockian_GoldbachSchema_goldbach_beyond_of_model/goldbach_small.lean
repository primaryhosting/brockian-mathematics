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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- The finite set of *Goldbach representations* of `n`: those `p ≤ n` such that both `p`
and `n - p` are prime. -/

theorem goldbach_small (n : ℕ) (h4 : 4 ≤ n) (h : n ≤ 200) (hev : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  have hdec : ∀ m ∈ Finset.range 201, 4 ≤ m → m % 2 = 0 →
      ∃ p ∈ Finset.range 201, ∃ q ∈ Finset.range 201,
        Nat.Prime p ∧ Nat.Prime q ∧ p + q = m := by decide
  have hmem : n ∈ Finset.range 201 := Finset.mem_range.mpr (by omega)
  obtain ⟨p, _, q, _, hp, hq, hpq⟩ :=
    hdec n hmem h4 (Nat.even_iff.mp hev)
  exact ⟨p, q, hp, hq, hpq⟩

/-- Combining the schema with the finite verification: a counting model whose threshold is at
most `202` yields the full Goldbach conjecture for all even `n ≥ 4`. -/
