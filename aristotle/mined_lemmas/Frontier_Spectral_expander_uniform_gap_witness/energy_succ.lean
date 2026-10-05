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

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1` in place `i`). -/

lemma energy_succ {k : ℕ} (f : Cube (k + 1) → ℝ) :
    energy (k + 1) f
      = 2 * (∑ y : Cube k, (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2)
        + energy k (fun y => f (Fin.cons 0 y)) + energy k (fun y => f (Fin.cons 1 y)) := by
  have h01 : (0 : ZMod 2) + 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have key : ∀ y : Cube k,
      (∑ i : Fin (k + 1), (f (Fin.cons 0 y) - f (Fin.cons 0 y + cubeE i)) ^ 2)
        + (∑ i : Fin (k + 1), (f (Fin.cons 1 y) - f (Fin.cons 1 y + cubeE i)) ^ 2)
      = 2 * (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2
        + ((∑ j : Fin k, (f (Fin.cons 0 y) - f (Fin.cons 0 (y + cubeE j))) ^ 2)
          + (∑ j : Fin k, (f (Fin.cons 1 y) - f (Fin.cons 1 (y + cubeE j))) ^ 2)) := by
    intro y
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [cons_add_cubeE_zero, cons_add_cubeE_succ, h01, h11]
    ring
  unfold energy
  rw [cube_sum_succ (fun x => ∑ i : Fin (k + 1), (f x - f (x + cubeE i)) ^ 2)]
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- Poincaré inequality on the hypercube (spectral gap `2`, in quadratic form). -/
