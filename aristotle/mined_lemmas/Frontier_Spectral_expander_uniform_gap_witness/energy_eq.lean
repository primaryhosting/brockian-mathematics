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

lemma energy_eq {k : ℕ} (f : Cube k → ℝ) :
    energy k f = 2 * ((k : ℝ) * (∑ x : Cube k, f x ^ 2)
      - ∑ x : Cube k, ∑ i : Fin k, f x * f (x + cubeE i)) := by
  have hpt : ∀ x : Cube k, ∑ i : Fin k, (f x - f (x + cubeE i)) ^ 2
      = ((k : ℝ) * f x ^ 2 + ∑ i : Fin k, f (x + cubeE i) ^ 2)
        - 2 * ∑ i : Fin k, f x * f (x + cubeE i) := by
    intro x
    have hexp : ∀ i : Fin k, (f x - f (x + cubeE i)) ^ 2
        = f x ^ 2 + f (x + cubeE i) ^ 2 - 2 * (f x * f (x + cubeE i)) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold energy
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_sum_shift (fun x => f x ^ 2)]
  ring

