/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

section Core

variable {d : ℕ}

/-- Two antitone real sequences monovary. -/

lemma monovary_of_antitone {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    Monovary mu nu := by
  intro i j hij
  rcases le_total i j with h | h
  · exact absurd (hnu h) (not_le.2 hij)
  · exact hmu h

/-- The bilinear form of two antitone sequences against a doubly stochastic matrix is
maximised by the diagonal (identity) pairing.  This combines Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) with the rearrangement inequality
(`Monovary.sum_mul_comp_perm_le_sum_mul`). -/
