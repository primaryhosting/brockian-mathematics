import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/

theorem schrodingerOp_topologicalClosure_of_weakRegularity [CompleteSpace H]
    {A V : H →L[ℂ] H} (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hV : WeaklyRegularPotential V) {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    (opGraph (schrodingerOp A V) D).topologicalClosure = opGraph (schrodingerOp A V) ⊤ := by
  refine topologicalClosure_opGraph ?_ hD
  intro x y
  simp only [schrodingerOp, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    hA x y, hV x y]

end Brockian.Weyl.DeficiencyODE

