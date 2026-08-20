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

lemma sum_chi {k : ℕ} (y : Cube k) :
    ∑ x : Cube k, chi y x = if y = 0 then (2 : ℝ) ^ k else 0 := by
  have h : ∑ x : Cube k, chi y x = ∏ i : Fin k, (if y i = 0 then (2 : ℝ) else 0) :=
    calc ∑ x : Cube k, chi y x = ∑ x : Cube k, ∏ i : Fin k, sgn (y i * x i) := rfl
      _ = ∏ i : Fin k, ∑ t : ZMod 2, sgn (y i * t) :=
          (Fintype.prod_sum (fun (i : Fin k) (t : ZMod 2) => sgn (y i * t))).symm
      _ = ∏ i : Fin k, (if y i = 0 then (2 : ℝ) else 0) :=
          Finset.prod_congr rfl (fun i _ => sum_sgn_mul (y i))
  rw [h]
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [if_neg hy]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hy (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Completeness of the character system: a vector orthogonal to every character is zero. -/
