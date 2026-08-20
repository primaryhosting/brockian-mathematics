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
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem countable_level (b : Ordinal.{0}) : {x : TreeNode | tlvl x = b}.Countable := by
  classical
  by_cases hb : b < ω₁
  · obtain ⟨j, hj⟩ := Set.countable_iff_exists_injOn.1 ((lt_omega1_iff_countable b).1 hb)
    set L : Set TreeNode := {x : TreeNode | tlvl x = b} with hL
    set phi : TreeNode → Set (ℕ × ℕ) :=
      fun x => {q | ∃ e < b, x.1.2 e ≠ E b e ∧ q = (j e, x.1.2 e)} with hphi
    have key : ∀ x ∈ L, ∀ y ∈ L, phi x = phi y → ∀ e < b, x.1.2 e ≠ E b e →
        x.1.2 e = y.1.2 e := by
      intro x _ y _ hxy e he hne
      have hmem : (j e, x.1.2 e) ∈ phi x := ⟨e, he, hne, rfl⟩
      rw [hxy] at hmem
      obtain ⟨e', he', -, hEq⟩ := hmem
      have h1 : j e = j e' := congrArg Prod.fst hEq
      have h2 : e = e' := hj he he' h1
      have h3 : x.1.2 e = y.1.2 e' := congrArg Prod.snd hEq
      rw [h3, h2]
    have hinj : Set.InjOn phi L := by
      intro x hx y hy hxy
      refine node_ext (by rw [hx, hy]) ?_
      intro e he
      rw [hx] at he
      by_cases h1 : x.1.2 e = E b e
      · by_cases h2 : y.1.2 e = E b e
        · rw [h1, h2]
        · exact (key y hy x hx hxy.symm e he h2).symm
      · exact key x hx y hy hxy e he h1
    refine Set.countable_of_injective_of_countable_image hinj ?_
    refine (Set.countable_setOf_finite_subset (Set.countable_univ (α := ℕ × ℕ))).mono ?_
    rintro s ⟨x, hx, rfl⟩
    refine ⟨?_, Set.subset_univ _⟩
    have hfin : {e : Ordinal.{0} | e < b ∧ x.1.2 e ≠ E b e}.Finite := by
      have := coh_node x
      rw [hx] at this
      exact this
    refine (hfin.image (fun e => (j e, x.1.2 e))).subset ?_
    rintro q ⟨e, he, hne, rfl⟩
    exact ⟨e, ⟨he, hne⟩, rfl⟩
  · have : {x : TreeNode | tlvl x = b} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hEq
      exact hb (hEq ▸ tlvl_lt_omega1 x)
    rw [this]
    exact Set.countable_empty

/-! ### Every level is nonempty -/

