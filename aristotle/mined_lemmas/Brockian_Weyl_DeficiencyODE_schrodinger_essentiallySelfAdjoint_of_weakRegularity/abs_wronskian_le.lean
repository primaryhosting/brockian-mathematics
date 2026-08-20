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

lemma abs_wronskian_le (c : ℤ → ℂ) (n : ℤ) :
    |wronskian c n| ≤ (‖c (n + 1)‖ ^ 2 + ‖c n‖ ^ 2) / 2 := by
  have h1 : |wronskian c n| ≤ ‖c (n + 1) * (starRingEnd ℂ) (c n)‖ := by
    simpa [wronskian] using Complex.abs_im_le_norm (c (n + 1) * (starRingEnd ℂ) (c n))
  have h2 : ‖c (n + 1) * (starRingEnd ℂ) (c n)‖ = ‖c (n + 1)‖ * ‖c n‖ := by
    rw [norm_mul, RCLike.norm_conj]
  nlinarith [sq_nonneg (‖c (n + 1)‖ - ‖c n‖), norm_nonneg (c (n + 1)), norm_nonneg (c n)]

