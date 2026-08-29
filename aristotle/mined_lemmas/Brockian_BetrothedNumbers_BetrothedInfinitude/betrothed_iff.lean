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

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

/-! ## Basic definitions

Everything below is developed from first principles (no imports), so that the
module docstring above can legally be the first thing in the file. -/

/-- The predicate selecting the positive divisors of `n`. -/

theorem betrothed_iff {m n : Nat} (hm : 1 < m) (hn : 1 < n) :
    Betrothed m n ↔ m ≠ n ∧ quasiAliquot m = n ∧ quasiAliquot n = m := by
  have h1 := sigmaSum_eq_quasiAliquot_add hm
  have h2 := sigmaSum_eq_quasiAliquot_add hn
  constructor
  · rintro ⟨-, -, hne, hsm, hsn⟩
    exact ⟨hne, by omega, by omega⟩
  · rintro ⟨hne, hqm, hqn⟩
    exact ⟨hm, hn, hne, by omega, by omega⟩

/-- Betrothedness is symmetric. -/
