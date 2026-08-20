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

theorem essentiallySelfAdjoint_opGraph [CompleteSpace H] {S : H →L[ℂ] H}
    (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ) {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    EssentiallySelfAdjoint (opGraph S D) :=
  essentiallySelfAdjoint_of_defRange_dense (isSymmetricGraph_opGraph hS D)
    (c := Complex.I) (by simp) Complex.I_ne_zero
    (dense_defRange_opGraph hS hD (by simp) Complex.I_ne_zero)
    (dense_defRange_opGraph hS hD (by simp) (by simp))

/-- The adjoint of a bounded symmetric operator restricted to a dense core is the operator
itself, defined on all of `H`. -/
