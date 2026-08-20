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

/-
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- Two antitone functions monovary. -/

lemma sum_permMatrix_mul {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (mu nu : n → ℝ) :
    ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j) = ∑ i, mu i * nu (σ i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (σ i)]
  · simp [PEquiv.toMatrix_apply]
  · intro j _ hj
    simp [PEquiv.toMatrix_apply, hj.symm]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Rearrangement / Birkhoff step.** If `S` is doubly stochastic and `μ`, `ν` are antitone
weight sequences, then `∑ i j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i`. -/
