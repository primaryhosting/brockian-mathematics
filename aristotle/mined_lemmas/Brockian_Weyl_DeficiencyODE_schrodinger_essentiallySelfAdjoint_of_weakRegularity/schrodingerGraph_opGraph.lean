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

lemma schrodingerGraph_opGraph (A V : H →L[ℂ] H) (D : Submodule ℂ H) :
    schrodingerGraph V (opGraph A D) = opGraph (schrodingerOp A V) D := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := mem_perturbGraph_iff.mp hp
    exact ⟨hq.1, by simp [schrodingerOp, hq.2]⟩
  · intro hp
    refine mem_perturbGraph_iff.mpr ⟨(p.1, A p.1), ⟨hp.1, rfl⟩, ?_⟩
    have h2 : p.2 = A p.1 + V p.1 := by simpa [schrodingerOp] using hp.2
    exact Prod.ext rfl h2.symm

/-- **Bounded kinetic term.** A Schrödinger operator whose kinetic term `A` is a bounded
symmetric operator and whose potential `V` is weakly regular is essentially self-adjoint on any
dense core `D`. This is an unconditional instance of the previous theorem. -/
