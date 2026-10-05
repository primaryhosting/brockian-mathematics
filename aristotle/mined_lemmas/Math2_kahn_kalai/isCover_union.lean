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

lemma isCover_union {H : Finset (Finset α)} {k : ℕ} {W : Finset α} {G : Finset (Finset α)}
    (hG : IsCover G (nextH H k W)) : IsCover (coverU H k W ∪ G) H := by
  intro S hS
  by_cases hbig : k < 2 * (frag H S W).card
  · refine ⟨frag H S W, ?_, frag_subset W hS⟩
    refine Finset.mem_union_left _ ?_
    simp only [coverU, Finset.mem_image]
    exact ⟨S, by simp [bigG, Finset.mem_filter, hS, hbig], rfl⟩
  · have hmem : frag H S W ∈ nextH H k W := by
      simp only [nextH, Finset.mem_image, Finset.mem_filter]
      exact ⟨S, ⟨hS, hbig⟩, rfl⟩
    obtain ⟨T, hTG, hTsub⟩ := hG _ hmem
    exact ⟨T, Finset.mem_union_right _ hTG, hTsub.trans (frag_subset W hS)⟩

/-- A chosen edge of `H` inside `Z` (used to encode fragments). -/
