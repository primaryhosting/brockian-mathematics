/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Weaver's discrepancy-theoretic form `KS₂` of the Kadison–Singer problem, in dimension `d`,
with smallness parameter `ε` and discrepancy constant `C`.

Given finitely many vectors `v i` in `ℂ^d` which form a Parseval frame
(`∑ i, |⟪v i, x⟫|² = ‖x‖²` for all `x`, i.e. `∑ i, v i v i* = I`) and each of which is small
(`‖v i‖² ≤ ε`), the index set can be split into two halves each of which is a frame with
upper bound `C` (i.e. the operator norm of each of the two partial sums `∑ v i v i*` is at
most `C`).

The Marcus–Spielman–Srivastava theorem states that this holds for every `d` and every `ε > 0`
with `C = (1/√2 + √ε)²`. -/

theorem weaverKS2_of_one_le (d : ℕ) (ε C : ℝ) (hC : 1 ≤ C) : WeaverKS2 d ε C := by
  intro m v _ hpar
  refine ⟨Finset.univ, ?_, ?_⟩
  · intro x
    have hx : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    rw [hpar x]
    nlinarith
  · intro x
    have hx : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    simp only [Finset.compl_univ, Finset.sum_empty]
    nlinarith

/-- The one-dimensional case of Weaver's `KS₂`, for any constant `C ≥ 1/2 + ε/2`. -/
