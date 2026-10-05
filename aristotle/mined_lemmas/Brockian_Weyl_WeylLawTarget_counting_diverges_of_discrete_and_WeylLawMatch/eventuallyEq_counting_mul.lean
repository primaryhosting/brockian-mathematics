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

theorem eventuallyEq_counting_mul (μ : ℕ → ℝ) {d : ℝ} :
    (fun Λ : ℝ => (countingFunction μ Λ : ℝ) / Λ ^ (d / 2) * Λ ^ (d / 2))
      =ᶠ[atTop] fun Λ : ℝ => (countingFunction μ Λ : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  have hpos : (0 : ℝ) < Λ ^ (d / 2) := Real.rpow_pos_of_pos hΛ _
  field_simp

/-- **Target.** If the spectrum is discrete and satisfies a Weyl law with positive
Weyl constant `C` and positive dimension `d`, then the eigenvalue counting function
diverges to `+∞`.

(The discreteness hypothesis is kept because it is named in the statement being
discharged; the divergence already follows from the Weyl asymptotics alone.) -/
