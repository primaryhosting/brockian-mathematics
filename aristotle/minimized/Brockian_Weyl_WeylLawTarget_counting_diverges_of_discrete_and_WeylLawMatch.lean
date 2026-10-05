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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

/-- The spectrum given by the eigenvalue family `lam` is *discrete*: below every level `L`
there are only finitely many eigenvalues. -/

noncomputable def counting (lam : ℕ → ℝ) (L : ℝ) : ℕ := {i : ℕ | lam i ≤ L}.ncard

/-- Weyl-law asymptotics with constant `C` in dimension `d`:
`N(L) / (C * L ^ (d / 2)) → 1` as `L → ∞`. -/

def WeylLawMatch (lam : ℕ → ℝ) (C d : ℝ) : Prop :=
  Tendsto (fun L : ℝ => (counting lam L : ℝ) / (C * L ^ (d / 2))) atTop (𝓝 1)

/-- If the spectrum is discrete and matches the Weyl law with a positive constant `C` in a
positive dimension `d`, then the counting function diverges: `N(L) → ∞` as `L → ∞`.

(The discreteness hypothesis `hdisc` is part of the statement as requested; the divergence
itself already follows from the Weyl-law asymptotics.) -/
