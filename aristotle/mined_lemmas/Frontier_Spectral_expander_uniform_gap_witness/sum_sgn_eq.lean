import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2

/-- The basis vector flipping coordinate `i`. -/

lemma sum_sgn_eq {k : ℕ} (s : Cube k) : ∑ i, sgn (s i) = (k : ℝ) - 2 * wt s := by
  have h : ∀ i : Fin k, sgn (s i) = 1 - 2 * (if s i ≠ 0 then (1 : ℝ) else 0) := by
    intro i
    by_cases h : s i = 0 <;> norm_num [sgn, h]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [wt, Finset.sum_ite, mul_comm]

/-- Orthogonality: the characters sum to `0` away from the origin. -/
