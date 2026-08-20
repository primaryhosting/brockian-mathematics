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

def schrodingerGraph (V : H →L[ℂ] H) (G : OperatorGraph H) : OperatorGraph H := perturbGraph V G

/-- **Essential self-adjointness of a Schrödinger operator with a weakly regular potential.**

Let `T` be a symmetric, essentially self-adjoint kinetic term on a complex Hilbert space `H`
(for instance the free Hamiltonian `-Δ` on a core of smooth compactly supported functions), and
let `V` be a weakly regular potential, i.e. a symmetric potential which is merely bounded, with
no smoothness or continuity assumed. Then the Schrödinger operator `T + V`, defined on the same
domain, is essentially self-adjoint: the closure of its graph coincides with the graph of its
adjoint, equivalently both of its deficiency spaces are trivial. -/
