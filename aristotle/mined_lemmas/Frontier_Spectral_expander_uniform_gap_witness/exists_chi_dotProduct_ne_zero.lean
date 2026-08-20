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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/

lemma exists_chi_dotProduct_ne_zero {k : ℕ} {v : Cube k → ℝ} (hv : v ≠ 0) :
    ∃ y : Cube k, (∑ x : Cube k, chi y x * v x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  refine hv (funext fun x₀ => ?_)
  have key : ∑ x : Cube k, v x * (if x = x₀ then (2 : ℝ) ^ k else 0) = 0 := by
    have h1 : ∀ x : Cube k, (∑ y : Cube k, chi y x₀ * chi y x)
        = if x = x₀ then (2 : ℝ) ^ k else 0 := by
      intro x
      have h2 : ∀ y : Cube k, chi y x₀ * chi y x = chi (x₀ + x) y := by
        intro y
        rw [chi_add_left, chi_symm x₀ y, chi_symm x y]
      rw [Finset.sum_congr rfl (fun y _ => h2 y), sum_chi]
      by_cases h : x = x₀
      · subst h
        rw [if_pos rfl, if_pos ((cube_add_eq_zero_iff x x).mpr rfl)]
      · rw [if_neg h, if_neg (fun hh => h ((cube_add_eq_zero_iff x₀ x).mp hh).symm)]
    calc ∑ x : Cube k, v x * (if x = x₀ then (2 : ℝ) ^ k else 0)
        = ∑ x : Cube k, ∑ y : Cube k, chi y x₀ * (chi y x * v x) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← h1 x, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by ring)
      _ = ∑ y : Cube k, chi y x₀ * ∑ x : Cube k, chi y x * v x := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => (Finset.mul_sum _ _ _).symm)
      _ = 0 := by
          refine Finset.sum_eq_zero (fun y _ => ?_)
          rw [hc y, mul_zero]
  rw [Finset.sum_eq_single x₀ (fun b _ hb => by rw [if_neg hb, mul_zero])
    (fun h => absurd (Finset.mem_univ x₀) h), if_pos rfl] at key
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  simpa [h2] using key

