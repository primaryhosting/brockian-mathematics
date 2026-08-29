import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
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

namespace Math2

open Finset

variable {n : ℕ}

/-- The shadow of a family `𝒜` of finite sets: all the sets obtained from a member of `𝒜` by
deleting one element. -/

lemma mem_shadow_iff {𝒜 : Finset (Finset (Fin n))} {t : Finset (Fin n)} :
    t ∈ shadow 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∈ s, s.erase a = t := by
  rw [shadow_eq, Finset.mem_shadow_iff]

/-- The colexicographic (colex) order on finite sets: `s` is smaller than `t` when the largest
element in which they differ belongs to `t`. -/
