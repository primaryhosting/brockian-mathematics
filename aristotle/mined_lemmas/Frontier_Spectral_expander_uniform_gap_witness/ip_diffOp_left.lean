/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

variable {k : ℕ}

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `(ZMod 2)^k`. -/

lemma ip_diffOp_left (i : Fin k) (u v : (Fin k → ZMod 2) → ℝ) :
    ip u (diffOp i v) = ip (diffOp i u) v := by
  have h1 : ∑ x, u x * v (flipAt x i) = ∑ x, u (flipAt x i) * v x := by
    have h := sum_flipAt i (fun x => u (flipAt x i) * v x)
    simp only [flipAt_flipAt] at h
    exact h
  simp only [ip, diffOp, mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1]

/-- Every quadratic form `⟪v, D_i D_j v⟫` is nonnegative. -/
