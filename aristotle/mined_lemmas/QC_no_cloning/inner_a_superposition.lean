import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Auxiliary: from an orthonormal pair `a, b` we build the unit vector
`(3/5) • a + (4/5) • b`, whose inner product with `a` is `3/5`. -/

lemma inner_a_superposition (a b : H) (ha : ‖a‖ = 1)
    (hab : inner ℂ a b = (0 : ℂ)) :
    inner ℂ a ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b) = (3 / 5 : ℂ) := by
  have haa : inner ℂ a a = (1 : ℂ) := inner_self_of_unit a ha
  rw [inner_add_right, inner_smul_right, inner_smul_right, haa, hab]
  ring

/-- **No-cloning theorem.**  There is no unitary `U` on `H ⊗ H` (a linear isometry
equivalence, i.e. an inner-product preserving linear bijection) together with a fixed
"blank" unit vector `e₀` such that `U (ψ ⊗ e₀) = ψ ⊗ ψ` for every state (unit vector) `ψ`,
as soon as `H` contains two orthogonal unit vectors (i.e. `H` has dimension at least 2). -/
