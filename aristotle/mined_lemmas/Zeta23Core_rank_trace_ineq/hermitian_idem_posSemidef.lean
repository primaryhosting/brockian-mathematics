import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a matrix. -/

lemma hermitian_idem_posSemidef {R : Matrix n n 𝕜} (h : R.IsHermitian) (h2 : R * R = R) :
    R.PosSemidef := by
  have hR : R = Rᴴ * R := by rw [h, h2]
  rw [hR]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### The functional calculus toolkit -/

section CFC

variable {A : Matrix n n 𝕜}

