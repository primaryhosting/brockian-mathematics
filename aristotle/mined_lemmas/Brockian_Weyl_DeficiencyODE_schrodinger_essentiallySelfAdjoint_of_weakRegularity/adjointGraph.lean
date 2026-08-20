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

def adjointGraph {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) : Submodule ℂ (E × E) where
  carrier := {p : E × E | ∀ x : D, ⟪T x, p.1⟫_ℂ = ⟪(x : E), p.2⟫_ℂ}
  add_mem' := by
    intro p q hp hq x
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, hp x, hq x]
  zero_mem' := by intro x; simp
  smul_mem' := by
    intro c p hp x
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, hp x]

