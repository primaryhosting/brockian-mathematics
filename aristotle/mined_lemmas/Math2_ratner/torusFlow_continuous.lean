import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Topology

/-!
## Setting

We formalise Ratner's orbit-closure and (homogeneous) invariant-measure statements for
one-parameter unipotent flows in the **abelian** case, i.e. for a linear flow
`t ↦ x + f t` on a compact homogeneous space `X` of a connected abelian Lie group.
The model case is the linear flow with direction `v` on the torus `ℝⁿ / ℤⁿ`, which is
recorded below as `Math2.ratner_torus`.

The conclusions are exactly the conclusions of Ratner's theorems in this case:

* the closure of every orbit is the coset `x + H` of a **closed connected** subgroup `H`
  which contains the flow (orbit-closure theorem);
* the orbit closure carries an `H`-invariant, hence flow-invariant, probability measure,
  namely the image of the Haar probability measure of the compact group `H` (homogeneity
  of the natural invariant measure).
-/

section Abstract

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

/-- The orbit of `x` under the one-parameter flow `t ↦ x + f t`. -/

theorem torusFlow_continuous {n : ℕ} (v : Fin n → ℝ) : Continuous (torusFlow v) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)

/-- **Ratner's theorems for a linear flow on the torus `ℝⁿ / ℤⁿ`.**

The closure of the orbit `{x + t·v mod ℤⁿ : t ∈ ℝ}` is the coset `x + H` of a closed
connected subgroup `H` of the torus containing the flow, and it carries an `H`-invariant
(hence flow-invariant) probability measure. -/
