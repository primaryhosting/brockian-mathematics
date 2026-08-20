/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

/-- The support of a nearest-neighbour bond gate sitting on the bond `i` of the
spin chain `ℤ`: the two sites `i` and `i + 1`. -/

lemma reach_subset_cone_succ (gs : List (Gate N)) (S : Set ℤ) (r : ℕ) :
    reach gs (cone r S) ⊆ cone (r + 1) S := by
  rintro p (hp | ⟨g, _, hd, hp⟩)
  · obtain ⟨s, hs, hps⟩ := hp
    exact ⟨s, hs, by push_cast; omega⟩
  · -- the gate touches the cone, so its two sites are within distance one of it
    obtain ⟨q, hqg, hq⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨s, hs, hqs⟩ := hq
    refine ⟨s, hs, ?_⟩
    have h1 : p = g.bond ∨ p = g.bond + 1 := hp
    have h2 : q = g.bond ∨ q = g.bond + 1 := hqg
    have : |q - s| ≤ (r : ℤ) := hqs
    push_cast
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      subst h1 <;> subst h2 <;> rw [abs_le] at * <;> omega

