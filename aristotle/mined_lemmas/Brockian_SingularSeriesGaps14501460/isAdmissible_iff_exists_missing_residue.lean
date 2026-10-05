import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
finite set of integers `H`.  These are the local densities appearing in the singular
series `𝔖(H) = ∏_p (1 - nu H p / p) / (1 - 1/p)^{|H|}` of the Hardy–Littlewood
prime tuples conjecture. -/

theorem isAdmissible_iff_exists_missing_residue (H : Finset ℤ) :
    IsAdmissible H ↔ ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact exists_missing_residue_of_nu_lt H p (hH p hp)
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    exact nu_lt_of_missing_residue H p r hr

/-- **Admissibility criterion.**  A set of primes, each of which exceeds the size of
the set, is admissible.  (For small primes `p` the residue class `0` is missed,
because every element is a prime larger than `p`; for large primes `p > |H|` there
are simply too few elements to cover all `p` classes.) -/
