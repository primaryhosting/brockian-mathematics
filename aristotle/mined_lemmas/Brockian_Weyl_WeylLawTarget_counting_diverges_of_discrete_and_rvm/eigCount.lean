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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function attached to a sequence of eigenvalues
`lam : ℕ → ℝ`: `eigCount lam Λ` is the number of indices `n` with `lam n ≤ Λ`
(counted with multiplicity, i.e. one contribution per index).

If the sub-level set is infinite the `Set.ncard` convention returns `0`; under the
discreteness hypothesis used below the sub-level sets are always finite, so this
degenerate case never occurs. -/

noncomputable def eigCount (lam : ℕ → ℝ) (Λ : ℝ) : ℕ := {n : ℕ | lam n ≤ Λ}.ncard

/-- Discreteness of the spectrum: every sub-level set of the eigenvalue sequence is finite.
This is the abstract form of "the spectrum is discrete with finite multiplicities". -/
