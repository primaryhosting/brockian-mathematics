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

lemma norm_sub_I_smul_sq {D : Submodule ℂ E} {T : D →ₗ[ℂ] E} (hsym : IsSymmetricOp T) (x : D) :
    ‖T x - Complex.I • (x : E)‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  have him : (inner ℂ (T x) (x : E) : ℂ).im = 0 := by
    have h2 : (starRingEnd ℂ) (inner ℂ (T x) (x : E)) = inner ℂ (T x) (x : E) := by
      rw [inner_conj_symm]; exact (hsym x x).symm
    exact Complex.conj_eq_iff_im.mp h2
  rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul]
  simp [him, Complex.I_re, Complex.I_im]

/-- On the closure of the graph, `‖x‖ ≤ ‖y - i x‖`. -/
