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
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/

lemma nextH_capture {H : Finset (Finset α)} {k : ℕ} {W T : Finset α} (hT : T ∈ nextH H k W) :
    W ∪ T ∈ upSet H := by
  simp only [nextH, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hS1, _⟩, rfl⟩ := hT
  obtain ⟨S', hS'H, hS'sub, heq⟩ := frag_spec W hS1
  rw [upSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S', hS'H, ?_⟩
  rw [← heq]
  intro x hx
  by_cases hxW : x ∈ W
  · exact Finset.mem_union_left _ hxW
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxW⟩)

/-- Splitting `H`: edges with a large fragment are covered by `coverU`, the others are
covered by any cover of `nextH`. -/
