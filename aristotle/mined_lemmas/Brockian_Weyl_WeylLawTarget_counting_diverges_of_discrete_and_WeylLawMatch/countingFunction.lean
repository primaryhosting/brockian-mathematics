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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter Topology

/-- The eigenvalue counting function of a spectrum `μ : ℕ → ℝ`:
`countingFunction μ Λ` is the number of indices `n` with `μ n ≤ Λ`. -/

noncomputable def countingFunction (μ : ℕ → ℝ) (Λ : ℝ) : ℕ :=
  Set.ncard {n : ℕ | μ n ≤ Λ}

/-- Discreteness of the spectrum: only finitely many eigenvalues lie below any threshold. -/
