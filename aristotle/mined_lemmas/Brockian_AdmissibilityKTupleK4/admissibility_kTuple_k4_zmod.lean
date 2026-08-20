/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`p` is at least `2` and its only divisors are `1` and `p`. -/

theorem admissibility_kTuple_k4_zmod (p : ℕ) (hp : p.Prime) :
    ∃ a : ZMod p, ∀ h ∈ ({0, 2, 6, 8} : Finset ℕ), (h : ZMod p) ≠ a := by
  obtain ⟨a, ha, hall⟩ := AdmissibilityKTupleK4 p (isPrimeNat_of_prime hp)
  refine ⟨(a : ZMod p), ?_⟩
  intro h hh hcast
  have hmem : h ∈ [0, 2, 6, 8] := by
    fin_cases hh <;> simp
  have := hall h hmem
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha] at hcast
  exact this hcast

end Brockian

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

