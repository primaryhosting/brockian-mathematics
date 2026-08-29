/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → Bool

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

def consEquiv (k : ℕ) : Cube k × Bool ≃ Cube (k + 1) where
  toFun p := Fin.cons p.2 p.1
  invFun x := (Fin.tail x, x 0)
  left_inv := by rintro ⟨y, b⟩; simp [Fin.tail_cons]
  right_inv := by intro x; simp [Fin.cons_self_tail]

