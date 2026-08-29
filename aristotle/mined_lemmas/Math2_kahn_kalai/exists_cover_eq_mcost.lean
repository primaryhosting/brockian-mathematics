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

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Defs

/-!
Elementary finite-probability toolkit for `p`-random subsets: the expectation `Ex p f`,
the fact that the weights sum to one, and the "union of independent random sets" identity.
-/

namespace Math2

open Finset

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The expectation of `f` at a `p`-random subset of the ground set `s`. -/

lemma exists_cover_eq_mcost (p : ℝ) (H : Finset (Finset X)) :
    ∃ G, Covers G H ∧ cost p G = mcost p H := by
  have h := Finset.min'_mem ((coverFams H).image (cost p)) (coverFams_nonempty H)
  rw [Finset.mem_image] at h
  obtain ⟨G, hG, hGc⟩ := h
  simp only [coverFams, mem_filter, mem_univ, true_and] at hG
  exact ⟨G, hG, hGc⟩

