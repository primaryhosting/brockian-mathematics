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

lemma specM_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specM hA f * specM hA g = specM hA (fun x => f x * g x) := by
  simp only [specM, Matrix.mul_assoc]
  congr 1
  rw [← Matrix.mul_assoc ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ),
    unit_star_mul, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp

