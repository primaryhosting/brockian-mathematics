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

theorem ratner {X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (f : ℝ →+ X) (hf : Continuous f) (x : X) :
    ∃ H : AddSubgroup X,
      IsClosed (H : Set X) ∧ IsConnected (H : Set X) ∧ (∀ t : ℝ, f t ∈ H) ∧
      closure (flowOrbit f x) = (fun h => x + h) '' (H : Set X) ∧
      ∃ μ : Measure X, IsProbabilityMeasure μ ∧
        μ (closure (flowOrbit f x)) = 1 ∧
        (∀ h ∈ H, μ.map (fun y => y + h) = μ) ∧
        (∀ t : ℝ, μ.map (fun y => y + f t) = μ) := by
  obtain ⟨μ, hμ, hμ1, hμinv⟩ :=
    exists_invariant_probabilityMeasure_of_isClosed (flowGroup f) (flowGroup_isClosed f) x
  refine ⟨flowGroup f, flowGroup_isClosed f, flowGroup_isConnected f hf, mem_flowGroup f,
    closure_flowOrbit f x, μ, hμ, ?_, hμinv, fun t => hμinv _ (mem_flowGroup f t)⟩
  rw [closure_flowOrbit f x]
  exact hμ1

/-- The `n`-dimensional torus `ℝⁿ / ℤⁿ`, written as a product of circles `ℝ / ℤ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- The linear (unipotent) flow on the torus `ℝⁿ / ℤⁿ` with direction vector `v`. -/
