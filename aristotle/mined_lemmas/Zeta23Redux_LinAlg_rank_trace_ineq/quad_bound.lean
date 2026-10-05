import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
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

namespace Zeta23Redux.LinAlg

open Matrix Unitary

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace of a matrix. -/

lemma quad_bound {X M : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hM : M.IsHermitian) :
    2 * rtrace (X * M) - frobSq M ≤ frobSq X := by
  have h0 : 0 ≤ frobSq (X - M) := frobSq_nonneg _
  rw [frobSq_sub_herm hX hM] at h0
  linarith

/-! ## Spectral (functional) calculus for Hermitian matrices -/

variable {A : Matrix (Fin d) (Fin d) ℂ}

/-- `specM hA f` is the Hermitian matrix obtained by applying the real function `f` to the
eigenvalues of the Hermitian matrix `A`. -/
