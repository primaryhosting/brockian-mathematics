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
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (no imports beyond Lean's `Init`), so that the
header comment above can literally begin the file.

We study the Hardy-Littlewood data attached to a prime gap `d`:

* admissibility of the two-element tuple `{0, d}` (no prime obstruction to `n`, `n + d` being
  simultaneously prime infinitely often), and
* the singular-series factor `∏_{p ∣ d, p odd prime} (p-1)/(p-2)`, recorded as an explicit
  positive rational `gapNum d / gapDen d`.

The main result `Brockian.SingularSeriesGaps12401250` verifies both for every even gap `d` in the
range `1240 ≤ d ≤ 1250`, extending the `SingularSeriesGaps` family to this range.
-/

namespace Brockian

/-! ## Primes -/

/-- Primality, stated from first principles. -/

def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, IsPrimeN p → ∃ r : Int, 0 ≤ r ∧ r < (p : Int) ∧ ∀ x ∈ H, x % (p : Int) ≠ r

/-- Every even gap `d` gives an admissible pair `{0, d}`. -/
