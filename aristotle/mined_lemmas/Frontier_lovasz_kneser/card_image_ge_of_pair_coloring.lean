import Mathlib

/-!
# Covering the pairs of a finite set by intersecting families

This file contains the combinatorial core of the case `k = 2` of the Lovász–Kneser theorem.

A proper colouring of the Kneser graph `KG_{n,2}` is exactly a partition of the `2`-element
subsets of an `n`-element set into *intersecting families*.  Such a family is either contained
in a "star" (all its members share a common element) or is a "triangle" (and then has exactly
three members).  This dichotomy drives an induction showing that at least `n - 2` families are
needed.
-/

namespace Frontier

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A two-element finset containing `x` is `{x, y}` for some `y ≠ x`. -/

theorem card_image_ge_of_pair_coloring {γ : Type*} [DecidableEq γ] :
    ∀ (N : ℕ) (V : Finset ι), V.card = N → ∀ col : Finset ι → γ,
      (∀ a ∈ V.powersetCard 2, ∀ b ∈ V.powersetCard 2, Disjoint a b → col a ≠ col b) →
      V.card - 2 ≤ ((V.powersetCard 2).image col).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V hVN col hcol
    by_cases hsmall : V.card ≤ 2
    · omega
    push_neg at hsmall
    set C : Finset γ := (V.powersetCard 2).image col with hC
    by_cases hA : ∃ v ∈ V, ∃ g ∈ C, ∀ e ∈ V.powersetCard 2, col e = g → v ∈ e
    · -- Case A: some colour class is a star centred at `v`; delete `v` and induct.
      obtain ⟨v, hv, g, hg, hstar⟩ := hA
      set V' : Finset ι := V.erase v with hV'
      have hV'card : V'.card = V.card - 1 := Finset.card_erase_of_mem hv
      have hlt : V'.card < N := by omega
      have hsub : V'.powersetCard 2 ⊆ V.powersetCard 2 := by
        apply Finset.powersetCard_mono
        exact Finset.erase_subset _ _
      have hIH := ih V'.card hlt V' rfl col
        (fun a ha b hb hab => hcol a (hsub ha) b (hsub hb) hab)
      have hsub2 : (V'.powersetCard 2).image col ⊆ C.erase g := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨e, he, rfl⟩ := hx
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_image_of_mem _ (hsub he)⟩
        intro hcg
        have hve := hstar e (hsub he) hcg
        rw [Finset.mem_powersetCard] at he
        have := he.1 hve
        exact (Finset.notMem_erase v V) this
      have hcard2 := Finset.card_le_card hsub2
      rw [Finset.card_erase_of_mem hg] at hcard2
      have hgpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨g, hg⟩
      omega
    · -- Case B: every colour class is a triangle, so has at most three members.
      push_neg at hA
      have hfiber : ∀ g ∈ C, ((V.powersetCard 2).filter (fun e => col e = g)).card ≤ 3 := by
        intro g hg
        refine card_le_three_of_intersecting _ ?_ ?_ ?_
        · intro e he
          rw [Finset.mem_filter, Finset.mem_powersetCard] at he
          exact he.1.2
        · intro e he f hf
          rw [Finset.mem_filter] at he hf
          intro hdisj
          exact hcol e he.1 f hf.1 hdisj (he.2.trans hf.2.symm)
        · intro e he v hve
          rw [Finset.mem_filter, Finset.mem_powersetCard] at he
          have hvV : v ∈ V := he.1.1 hve
          obtain ⟨f, hf, hfg, hvf⟩ := hA v hvV g hg
          exact ⟨f, by rw [Finset.mem_filter]; exact ⟨hf, hfg⟩, hvf⟩
      have hsum : (V.powersetCard 2).card = ∑ g ∈ C, ((V.powersetCard 2).filter
          (fun e => col e = g)).card :=
        Finset.card_eq_sum_card_fiberwise (fun e he => Finset.mem_image_of_mem _ he)
      have hle : (V.powersetCard 2).card ≤ 3 * C.card := by
        rw [hsum]
        calc ∑ g ∈ C, ((V.powersetCard 2).filter (fun e => col e = g)).card
            ≤ ∑ _g ∈ C, 3 := Finset.sum_le_sum hfiber
          _ = 3 * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.card_powersetCard] at hle
      have h2 : 2 * (V.card.choose 2) = V.card * (V.card - 1) := two_mul_choose_two V.card
      -- arithmetic: `n (n-1) ≤ 6 c` and `n ≥ 3` force `c ≥ n - 2`
      by_contra hcon
      push_neg at hcon
      have hn : V.card * (V.card - 1) ≤ 6 * C.card := by omega
      have h3 : C.card + 3 ≤ V.card := by omega
      have h4 : 3 ≤ V.card := by omega
      obtain ⟨m, hm⟩ : ∃ m, V.card = m + 1 := ⟨V.card - 1, by omega⟩
      rw [hm] at hn h3 h4
      simp only [Nat.add_sub_cancel] at hn
      have h5 : m ≤ 5 := by nlinarith
      interval_cases m <;> omega

end Frontier

import Mathlib
import RequestProject.IntersectingCover

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

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two distinct such subsets are adjacent when they are disjoint. -/
