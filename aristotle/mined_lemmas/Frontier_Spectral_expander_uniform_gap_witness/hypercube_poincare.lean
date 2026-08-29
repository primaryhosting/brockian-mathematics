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

lemma hypercube_poincare (k : ℕ) (f : Cube k → ℝ) :
    4 * ((2 : ℝ) ^ k * ∑ x : Cube k, f x ^ 2 - (∑ x : Cube k, f x) ^ 2)
      ≤ (2 : ℝ) ^ k * energy k f := by
  revert f
  induction k with
  | zero =>
      intro f
      simp [energy, Finset.univ_unique]
  | succ k ih =>
      intro f
      set f0 : Cube k → ℝ := fun y => f (Fin.cons 0 y) with hf0
      set f1 : Cube k → ℝ := fun y => f (Fin.cons 1 y) with hf1
      have hsq : ∑ x : Cube (k + 1), f x ^ 2
          = (∑ y : Cube k, f0 y ^ 2) + ∑ y : Cube k, f1 y ^ 2 := by
        rw [cube_sum_succ (fun x => f x ^ 2), ← Finset.sum_add_distrib]
      have hsum : ∑ x : Cube (k + 1), f x
          = (∑ y : Cube k, f0 y) + ∑ y : Cube k, f1 y := by
        rw [cube_sum_succ f, ← Finset.sum_add_distrib]
      have hdiff : ∑ y : Cube k, (f0 y - f1 y)
          = (∑ y : Cube k, f0 y) - ∑ y : Cube k, f1 y := by
        rw [Finset.sum_sub_distrib]
      have hcs : ((∑ y : Cube k, f0 y) - ∑ y : Cube k, f1 y) ^ 2
          ≤ (2 : ℝ) ^ k * ∑ y : Cube k, (f0 y - f1 y) ^ 2 := by
        have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Cube k)))
          (f := fun y => f0 y - f1 y)
        rw [hdiff] at h
        simpa using h
      rw [hsq, hsum, energy_succ f, ← hf0, ← hf1]
      have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
      rw [hpow]
      nlinarith [ih f0, ih f1, hcs]

