/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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

/-- A finite set of integer shifts `H` *avoids* the prime `p` when the shifts do not cover
all residue classes modulo `p`. -/

def AvoidsPrime (H : Finset ℤ) (p : ℕ) : Prop :=
  ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- A finite set of integer shifts is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when for every prime `p` it omits at least one residue class
modulo `p`; equivalently, its singular series is nonzero. -/
