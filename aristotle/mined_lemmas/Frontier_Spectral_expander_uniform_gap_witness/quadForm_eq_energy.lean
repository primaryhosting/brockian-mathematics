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

lemma quadForm_eq_energy {k : ℕ} (f : Cube k → ℝ) :
    f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) = energy k f / 2 := by
  have h2 : ∀ x : Cube k, f x * ((k : ℝ) * f x - ∑ i : Fin k, f (x + cubeE i))
      = (k : ℝ) * f x ^ 2 - ∑ i : Fin k, f x * f (x + cubeE i) := by
    intro x
    rw [mul_sub, Finset.mul_sum]
    ring
  rw [dotProduct]
  simp only [lapMatrix_hypercube_mulVec_apply]
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_sub_distrib, ← Finset.mul_sum, energy_eq]
  ring

/-- Eigenvectors for nonzero eigenvalues have zero mean. -/
