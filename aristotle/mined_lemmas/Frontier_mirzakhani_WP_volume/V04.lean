/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

noncomputable def V04 (L₁ L₂ L₃ L₄ : ℝ) : ℝ :=
  2 * π ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2

/-- The Weil–Petersson volume polynomial of `M_{1,1}`.

We use the orbifold normalisation `V_{1,1}(L) = (L² + 4π²)/48` (so that `V_{1,1}(0) = π²/12`),
which is the one for which Mirzakhani's recursion is stated with its usual constants; the
generic one-holed torus has the elliptic involution as an automorphism, which accounts for
the factor `2` relative to the normalisation `(L² + 4π²)/24`. -/
