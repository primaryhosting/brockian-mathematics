/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of natural numbers is *admissible* when, for every prime `p`, its elements
omit at least one residue class modulo `p`.  This is exactly the classical condition under
which the singular series attached to the tuple is non-zero. -/

lemma modEq_two_of_admissible {H : Finset ℕ} (hH : IsAdmissible H) {x y : ℕ}
    (hx : x ∈ H) (hy : y ∈ H) : x ≡ y [MOD 2] := by
  obtain ⟨a, ha⟩ := hH 2 Nat.prime_two
  have key : ∀ a x y : ZMod 2, x ≠ a → y ≠ a → x = y := by decide
  have : (x : ZMod 2) = (y : ZMod 2) := key a _ _ (ha x hx) (ha y hy)
  exact (ZMod.natCast_eq_natCast_iff x y 2).mp this

/-- The two-element set `{0, d}` is admissible whenever `d` is even. -/
