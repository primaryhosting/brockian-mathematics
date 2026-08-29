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

import Mathlib

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace SierpinskiCovering

/-- `k` is a *Sierpiński number* if it is odd and `k * 2 ^ n + 1` is composite
(here: not prime) for every `n ≥ 1`. -/

theorem sierpinski_least_iff :
    IsLeast {k : ℕ | IsSierpinski k} 78557 ↔ ∀ k < 78557, ¬ IsSierpinski k := by
  constructor
  · rintro ⟨-, hlb⟩ k hk hks
    exact absurd (hlb hks) (by omega)
  · intro h
    refine ⟨SierpinskiProblem, ?_⟩
    intro k hk
    by_contra hlt
    exact h k (by omega) hk

end SierpinskiCovering
end Brockian

