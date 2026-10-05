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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PolignacPrimes

/-- A finite list of linear forms `a * x + b` (encoded as pairs `(a, b)`) is *admissible*
if for every prime `p` there is some `x` for which no form takes a value divisible by `p`. -/

def Admissible (L : List (ℕ × ℕ)) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ ab ∈ L, ¬ p ∣ (ab.1 * x + ab.2)

/-- **Dickson's conjecture** (the prime `k`-tuples hypothesis in its qualitative form):
for every admissible finite family of linear forms with positive leading coefficients,
there are infinitely many `x` at which all the forms are simultaneously prime. -/
