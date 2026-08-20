import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A `k`-tuple `H : Fin k → ℕ` is *admissible* when, for every prime `p`, the values
`H i` do not cover all residue classes modulo `p`. -/

theorem exists_missing_residue_of_card_lt {k : ℕ} (H : Fin k → ℕ) (p : ℕ) [NeZero p]
    (hp : k < p) : ∃ r : ZMod p, ∀ i : Fin k, (H i : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsurj : Function.Surjective (fun i : Fin k => ((H i : ZMod p))) := by
    intro r
    obtain ⟨i, hi⟩ := hcon r
    exact ⟨i, hi⟩
  have hcard := Fintype.card_le_of_surjective _ hsurj
  simp only [ZMod.card, Fintype.card_fin] at hcard
  omega

/-- Consequently, admissibility of a `k`-tuple only has to be checked at the primes `p ≤ k`. -/
