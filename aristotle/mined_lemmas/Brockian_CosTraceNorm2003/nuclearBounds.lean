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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Brockian

/-- The set of admissible bounds for the nuclear (trace) norm of a real matrix `A`:
`c` belongs to it iff `A` can be written as a finite sum of rank-one matrices
`u i ⊗ v i` whose total "product of Euclidean norms" is at most `c`. -/

def nuclearBounds {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Set ℝ :=
  {c : ℝ | ∃ (r : ℕ) (u : Fin r → Fin n → ℝ) (v : Fin r → Fin m → ℝ),
      (∀ j k, A j k = ∑ i, u i j * v i k) ∧
      ∑ i, Real.sqrt (∑ j, (u i j) ^ 2) * Real.sqrt (∑ k, (v i k) ^ 2) ≤ c}

/-- The nuclear norm (= trace norm = sum of the singular values) of a real matrix,
defined variationally as the infimum of the total rank-one mass of a decomposition. -/
