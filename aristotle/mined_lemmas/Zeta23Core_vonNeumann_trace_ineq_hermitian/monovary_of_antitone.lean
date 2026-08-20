/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

lemma monovary_of_antitone {N : ℕ} {a b : Fin N → ℝ} (ha : Antitone a) (hb : Antitone b) :
    Monovary a b := by
  intro i j h
  rcases le_total i j with hij | hij
  · exact absurd (hb hij) (not_le.2 h)
  · exact ha hij

/-- Rearrangement bound for a doubly stochastic weight matrix: a doubly stochastic average of
the products of two families of reals is at most the sum of the products of their decreasing
rearrangements. -/
