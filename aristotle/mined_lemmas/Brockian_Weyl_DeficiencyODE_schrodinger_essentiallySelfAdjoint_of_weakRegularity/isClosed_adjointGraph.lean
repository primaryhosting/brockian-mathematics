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

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma isClosed_adjointGraph {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) :
    IsClosed (adjointGraph T : Set (E × E)) := by
  have : (adjointGraph T : Set (E × E)) =
      ⋂ x : D, {p : E × E | ⟪T x, p.1⟫_ℂ = ⟪(x : E), p.2⟫_ℂ} := by
    ext p; simp [adjointGraph, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun x => ?_
  have h1 : Continuous fun p : E × E => ⟪T x, p.1⟫_ℂ := continuous_const.inner continuous_fst
  have h2 : Continuous fun p : E × E => ⟪(x : E), p.2⟫_ℂ := continuous_const.inner continuous_snd
  exact isClosed_eq h1 h2

