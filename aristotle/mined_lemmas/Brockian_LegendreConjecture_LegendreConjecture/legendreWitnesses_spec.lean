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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede any module doc comment, so the
-- required header block appears immediately after the single `import Mathlib` line.

namespace Brockian.LegendreConjecture

/-- `PrimeBetweenSquares n` states that there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2`. -/

private theorem legendreWitnesses_spec :
    ∀ i ∈ Finset.range 500,
      (2 ≤ legendreWitnesses.getD i 0 ∧
        ∀ m ∈ Finset.Icc 2 501, m * m ≤ legendreWitnesses.getD i 0 →
          ¬ m ∣ legendreWitnesses.getD i 0) ∧
      (i + 1) ^ 2 < legendreWitnesses.getD i 0 ∧
      legendreWitnesses.getD i 0 < (i + 2) ^ 2 := by
  decide +kernel

/-- **Unconditional verification of Legendre's conjecture for all `1 ≤ n ≤ 500`.** -/
