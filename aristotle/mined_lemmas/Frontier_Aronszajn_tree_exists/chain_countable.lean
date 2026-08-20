import Mathlib

/-!
# Construction of an Aronszajn tree

We build the classical (special) Aronszajn tree: nodes at level `α < ω₁` are strictly
increasing bounded functions `α → ℚ`, constructed by transfinite recursion so that each
level is countable and every node can be extended to any higher level while keeping a
prescribed rational bound.
-/

open Ordinal Cardinal Set Order
open scoped Classical

namespace Aronszajn

set_option autoImplicit false
set_option maxRecDepth 8000

/-- A node is (the total extension by `0` of) a function from a countable ordinal to `ℚ`. -/
abbrev Nd : Type 1 := Ordinal.{0} → ℚ

/-- `SBd f α q` says the values of `f` below `α` are bounded by some rational `< q`. -/

theorem chain_countable (b : Set Node) (hb : IsChain nle b) : b.Countable := by
  -- the height map is injective on a chain
  have hinj : Set.InjOn nht b := by
    intro x hx y hy hxy
    rcases eq_or_ne x y with h | h
    · exact h
    · rcases hb hx hy h with h1 | h1
      · exact absurd hxy (ne_of_lt (nht_lt_of_nle h1 h))
      · exact absurd hxy.symm (ne_of_lt (nht_lt_of_nle h1 (Ne.symm h)))
  refine (Set.mapsTo_image nht b).countable_of_injOn hinj ?_
  -- the set of heights is countable
  set H : Set Ordinal.{0} := nht '' b with hH
  set H' : Set Ordinal.{0} := {a ∈ H | ∃ a' ∈ H, a < a'} with hH'
  have hsplit : H ⊆ H' ∪ (H \ H') := by
    intro a ha
    by_cases h : a ∈ H'
    · exact Or.inl h
    · exact Or.inr ⟨ha, h⟩
  refine Set.Countable.mono hsplit (Set.Countable.union ?_ ?_)
  · -- `H'` injects into `ℚ`
    classical
    set F : Ordinal.{0} → ℚ := fun a =>
      if h : ∃ y, y ∈ b ∧ a < nht y then nfun h.choose a else 0 with hF
    have hFspec : ∀ a ∈ H', ∃ y, y ∈ b ∧ a < nht y ∧ F a = nfun y a := by
      intro a ha
      have h : ∃ y, y ∈ b ∧ a < nht y := by
        obtain ⟨-, a', ⟨y, hy, rfl⟩, haa'⟩ := ha
        exact ⟨y, hy, haa'⟩
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
    have hmono : ∀ a ∈ H', ∀ a' ∈ H', a < a' → F a < F a' := by
      intro a ha a' ha' haa'
      obtain ⟨y, hy, hy1, hy2⟩ := hFspec a ha
      obtain ⟨z, hz, hz1, hz2⟩ := hFspec a' ha'
      -- pass to the larger of `y` and `z`
      have key : ∃ w ∈ b, a < nht w ∧ a' < nht w ∧ nfun y a = nfun w a ∧ nfun z a' = nfun w a' := by
        rcases eq_or_ne y z with rfl | hne
        · exact ⟨y, hy, hy1, hz1, rfl, rfl⟩
        · rcases hb hy hz hne with h1 | h1
          · exact ⟨z, hz, haa'.trans hz1, hz1, h1.2 a hy1, rfl⟩
          · exact ⟨y, hy, hy1, lt_of_lt_of_le hz1 h1.1, rfl, h1.2 a' hz1⟩
      obtain ⟨w, -, hw1, hw2, hw3, hw4⟩ := key
      rw [hy2, hz2, hw3, hw4]
      exact nfun_mono w haa' hw2
    have hinj' : Set.InjOn F H' := by
      intro a ha a' ha' hFa
      rcases lt_trichotomy a a' with h | h | h
      · exact absurd hFa (ne_of_lt (hmono a ha a' ha' h))
      · exact h
      · exact absurd hFa.symm (ne_of_lt (hmono a' ha' a ha h))
    exact (Set.mapsTo_univ F H').countable_of_injOn hinj' Set.countable_univ
  · -- at most one maximal height
    have : (H \ H').Subsingleton := by
      intro a ha a' ha'
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact ha.2 ⟨ha.1, a', ha'.1, h⟩
      · exact ha'.2 ⟨ha'.1, a, ha.1, h⟩
    exact this.countable

end Aronszajn

import Mathlib
import RequestProject.Aronszajn
import RequestProject.AronszajnTree

-- (Lean requires `import` lines to come first in a file; the header comment follows.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
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
set_option pp.piBinderTypes true

set_option grind.warning false

open Ordinal

namespace Frontier

/-- **There exists an Aronszajn tree.**

We exhibit a type `T` with a partial order `le` and a height function `ht` such that:

* `le` is a partial order (reflexive, transitive, antisymmetric);
* every node has height `< ω₁`, and `le`-smaller nodes have strictly smaller height;
* for every node `x` and every `β < ht x` there is a *unique* predecessor of `x` of
  height `β` (so the predecessors of `x` are well-ordered with order type `ht x`,
  i.e. `T` is a tree and `ht` is its height function);
* every level `β < ω₁` is nonempty, so the tree has height exactly `ω₁`;
* every level is countable;
* every chain (in particular every branch) is countable, so there is no uncountable
  branch.
-/
