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

lemma mem_cands {H : Finset (Finset α)} {S W T : Finset α} :
    T ∈ cands H S W ↔ ∃ S' ∈ H, S' ⊆ W ∪ S ∧ S' \ W = T := by
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S', ⟨h1, h2⟩, h3⟩; exact ⟨S', h1, h2, h3⟩
  · rintro ⟨S', h1, h2, h3⟩; exact ⟨S', ⟨h1, h2⟩, h3⟩

/-- A minimum `(S, W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`,
`S' ⊆ W ∪ S`. -/
