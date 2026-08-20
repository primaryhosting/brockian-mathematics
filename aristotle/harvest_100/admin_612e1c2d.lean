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
def IsAdmissibleKTuple (k : ℕ) (H : Fin k → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i : Fin k, (H i : ZMod p) ≠ r

/-- Key intermediate lemma: a `k`-tuple automatically misses a residue class modulo any
modulus `p` with `k < p`, simply because there are too few values to be surjective. -/
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
theorem isAdmissibleKTuple_of_small_primes {k : ℕ} (H : Fin k → ℕ)
    (h : ∀ p : ℕ, p.Prime → p ≤ k → ∃ r : ZMod p, ∀ i : Fin k, (H i : ZMod p) ≠ r) :
    IsAdmissibleKTuple k H := by
  intro p hp
  rcases le_or_gt p k with hpk | hpk
  · exact h p hp hpk
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact exists_missing_residue_of_card_lt H p hpk

/-- **Admissibility for 4-tuples.** The prime 4-tuple pattern `(0, 2, 6, 8)` is admissible:
for every prime `p` the four shifts omit at least one residue class modulo `p`. -/
theorem AdmissibilityKTupleK4 : IsAdmissibleKTuple 4 ![0, 2, 6, 8] := by
  apply isAdmissibleKTuple_of_small_primes
  intro p hp hpk
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p
  · refine ⟨1, ?_⟩
    decide
  · refine ⟨1, ?_⟩
    decide
  · exact absurd hp (by decide)

end Brockian

