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

lemma summable_repr_sq (b : HilbertBasis ℤ ℂ E) (u : E) :
    Summable fun n => ‖b.repr u n‖ ^ 2 := by
  have h := lp.memℓp (b.repr u)
  rw [Memℓp] at h
  simp at h
  convert h using 2 with n

/-- **Triviality of the deficiency subspaces.**  For any non-real `z`, a vector `u` with
`⟪H x, u⟫ = z ⟪x, u⟫` for all `x` in the domain vanishes.  This is where the deficiency
difference equation ('deficiency ODE') is solved. -/
