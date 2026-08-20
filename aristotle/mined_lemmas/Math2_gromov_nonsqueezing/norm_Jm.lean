/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-! ## The standard symplectic vector space `ℝ^{2n}`

We model `ℝ^{2n}` as the Euclidean space indexed by `Fin n × Fin 2`, where for each
`i : Fin n` the coordinate `(i,0)` is the position `x i` and `(i,1)` is the momentum `y i`.
-/

/-- The standard `2n`-dimensional Euclidean/symplectic vector space. -/
abbrev V (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form `ω(u,v) = ∑ i, (u_{x i} v_{y i} - u_{y i} v_{x i})`. -/

lemma norm_Jm {n : ℕ} (z : V n) : ‖Jm z‖ = ‖z‖ := by
  rw [← Real.sqrt_mul_self (norm_nonneg (Jm z)), ← Real.sqrt_mul_self (norm_nonneg z),
    ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, inner_Jm_Jm]

