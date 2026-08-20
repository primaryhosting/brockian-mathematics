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
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other token in a file
-- (a module doc comment before an `import` is a syntax error), so the required
-- header comment is placed immediately after the single `import Mathlib` line.

open Filter Set
open scoped Topology

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl law: a nondecreasing sequence of real
"eigenvalues" `mu 0 ≤ mu 1 ≤ ⋯` diverging to `+∞`.  This is the standard shape
of the spectrum of an operator with compact resolvent. -/
structure Candidate where
  /-- The candidate eigenvalue sequence, listed with multiplicity. -/
  mu : ℕ → ℝ
  /-- The eigenvalues are listed in nondecreasing order. -/
  mono : Monotone mu
  /-- The eigenvalues tend to `+∞`; equivalently, the spectrum is discrete. -/
  diverges : Tendsto mu atTop atTop

/-- The eigenvalue counting function `N(λ) = #{n | mu n ≤ λ}` of a candidate
spectrum. -/

theorem counting_diverges_of_candidate (C : Candidate) :
    Tendsto (countingFn C) atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  filter_upwards [eventually_ge_atTop (C.mu k)] with lam hlam
  have hsub : Set.Iio k ⊆ {n : ℕ | C.mu n ≤ lam} := fun n hn =>
    le_trans (C.mono (le_of_lt hn)) hlam
  calc k = (Set.Iio k).ncard := (Set.ncard_Iio_nat k).symm
    _ ≤ ({n : ℕ | C.mu n ≤ lam}).ncard :=
        Set.ncard_le_ncard hsub (finite_sublevel C lam)

end Brockian.Weyl.WeylLawTarget

