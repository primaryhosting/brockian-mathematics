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

theorem evolve_mem_cone (L : List (List (Gate N))) (hL : ∀ l ∈ L, IsLayer l)
    {S : Set ℤ} {x : A} (hx : x ∈ N.loc S) :
    evolve L x ∈ N.loc (cone L.length S) := by
  induction L generalizing S x with
  | nil => exact N.mono (subset_cone 0 S) hx
  | cons l ls ih =>
      have hl : IsLayer l := hL l List.mem_cons_self
      have h1 : conjList l x ∈ N.loc (reach l S) := conjList_mem hl hx
      have h2 : evolve ls (conjList l x) ∈ N.loc (cone ls.length (reach l S)) :=
        ih (fun m hm => hL m (List.mem_cons_of_mem _ hm)) h1
      refine N.mono ?_ h2
      -- `reach l S ⊆ cone 1 S`, and cones compose
      have hr : reach l S ⊆ cone 1 S := by
        have := reach_subset_cone_succ (N := N) l S 0
        intro p hp
        exact this (by
          rcases hp with hp | ⟨g, hg, hd, hpg⟩
          · exact Or.inl (subset_cone 0 S hp)
          · refine Or.inr ⟨g, hg, ?_, hpg⟩
            intro hcon
            exact hd (hcon.mono_right (subset_cone 0 S)))
      intro p hp
      obtain ⟨q, hq, hpq⟩ := hp
      obtain ⟨s, hs, hqs⟩ := hr hq
      refine ⟨s, hs, ?_⟩
      simp only [List.length_cons]
      push_cast
      rw [abs_le] at *
      omega

/-- **Lieb–Robinson bound (finite propagation speed / light cone form).**

For a quantum spin chain with a discrete-time dynamics given by `L.length` layers
of nearest-neighbour gates, an observable `x` supported in a region `S` evolves
into an observable supported within distance `L.length` of `S`.  Consequently, if
every site of `S` is at distance strictly greater than `L.length` from every site
of a region `T`, then the evolved observable commutes exactly with every
observable `y` supported in `T`: outside the light cone the commutator vanishes. -/
