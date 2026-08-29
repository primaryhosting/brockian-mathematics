import Mathlib
/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Singular value decomposition -/

/-- Every square complex matrix admits a singular value decomposition
`M = U * diagonal s * V` with `U`, `V` unitary and `s` a nonnegative real vector. -/

lemma toLp_coeff_self (ψ : EuclideanSpace ℂ (n × n)) :
    (WithLp.toLp 2 (fun p : n × n => (Matrix.of fun i k => ψ (i, k)) p.1 p.2)) = ψ := rfl

/-- **Uhlmann's theorem**: the fidelity `tr √(√ρ σ √ρ)` is the maximum of the overlap
`|⟪ψ, ξ⟫|` taken over all purifications `ψ` of `ρ` and `ξ` of `σ`. -/
