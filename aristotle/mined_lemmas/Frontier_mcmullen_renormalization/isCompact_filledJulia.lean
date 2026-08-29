/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

theorem isCompact_filledJulia (f : ℂ → ℂ) (hf : Continuous f) (R : ℝ) :
    IsCompact (filledJulia f R) := by
  refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_filledJulia f hf R) ?_
  intro z hz
  have := hz 0
  simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- The filled Julia set is forward invariant. -/
