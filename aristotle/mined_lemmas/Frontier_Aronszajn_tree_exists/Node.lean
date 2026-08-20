/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem Node.chains_countable (C : Set Node) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  by_contra hunc
  have hunb : ∀ b < omega1, ∃ p ∈ C, b < p.lvl := by
    intro b hb
    by_contra hcon
    push_neg at hcon
    apply hunc
    refine Set.countable_of_injective_of_countable_image (f := Node.lvl) ?_ ?_
    · intro p hp q hq h
      by_contra hne
      rcases hC hp hq hne with hle | hle
      · exact absurd h (ne_of_lt (Node.lvl_lt_of_lt (lt_of_le_of_ne hle hne)))
      · exact absurd h.symm (ne_of_lt (Node.lvl_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hne))))
    · refine Set.Countable.mono ?_ (countable_Iio_of_lt (succ_lt_omega1 hb))
      rintro y ⟨p, hp, rfl⟩
      exact lt_of_le_of_lt (hcon p hp) (ord_lt_add_one b)
  set F : Ordinal → ℕ := fun x => if h : ∃ p, p ∈ C ∧ x < p.lvl then h.choose.f x else 0 with hF
  have hFval : ∀ p ∈ C, ∀ x < p.lvl, F x = p.f x := by
    intro p hp x hx
    have hex : ∃ p, p ∈ C ∧ x < p.lvl := ⟨p, hp, hx⟩
    rw [hF]
    simp only [dif_pos hex]
    obtain ⟨hqC, hqx⟩ := hex.choose_spec
    by_cases hpq : hex.choose = p
    · rw [hpq]
    · rcases hC hqC hp hpq with hle | hle
      · exact hle.2 x hqx
      · exact (hle.2 x hx).symm
  have hFfin : ∀ b < omega1, ∀ v : ℕ, {x | x < b ∧ F x = v}.Finite := by
    intro b hb v
    obtain ⟨p, hp, hbp⟩ := hunb b hb
    refine Set.Finite.subset (p.finOne v) ?_
    rintro x ⟨hx, hv⟩
    have hxp : x < p.lvl := lt_trans hx hbp
    exact ⟨hxp, by rw [← hFval p hp x hxp]; exact hv⟩
  have hfib : ∀ v : ℕ, {x | x < omega1 ∧ F x = v}.Finite := by
    intro v
    by_contra hinf
    rw [Set.not_finite] at hinf
    have e : ℕ ↪ {x : Ordinal // x ∈ {x | x < omega1 ∧ F x = v}} :=
      Set.Infinite.natEmbedding _ hinf
    set s : ℕ → Ordinal := fun n => (e n : Ordinal) with hs
    have hsinj : Function.Injective s := by
      intro m n hmn
      exact e.injective (Subtype.ext hmn)
    have hslt : ∀ n, s n < omega1 := fun n => (e n).2.1
    have hsup : iSup s < omega1 := iSup_lt_omega1 hslt
    have hb : iSup s + 1 < omega1 := succ_lt_omega1 hsup
    have hsub : Set.range s ⊆ {x | x < iSup s + 1 ∧ F x = v} := by
      rintro y ⟨n, rfl⟩
      exact ⟨lt_of_le_of_lt (Ordinal.le_iSup s n) (ord_lt_add_one _), (e n).2.2⟩
    exact (Set.infinite_range_of_injective hsinj).mono hsub (hFfin _ hb v)
  have hcount : (Set.Iio omega1).Countable := by
    refine Set.Countable.mono ?_ (Set.countable_iUnion (fun v : ℕ => (hfib v).countable))
    intro x hx
    exact Set.mem_iUnion.mpr ⟨F x, hx, rfl⟩
  exact not_countable_Iio_omega1 hcount

/-! ### The main theorem -/

/-- `lvl` exhibits the partially ordered set `T` as an *Aronszajn tree*: the predecessors of
any node `x` form a chain containing exactly one node at each level below `lvl x` (so `lvl x`
is the height of `x`, see `IsAronszajnTree.bijOn_pred`), every level below `ω₁` is nonempty
(so the tree has height `ω₁`), every level is countable, and there is no uncountable chain
(in particular, no uncountable branch). -/
structure IsAronszajnTree (T : Type*) [PartialOrder T] (lvl : T → Ordinal) : Prop where
  /-- every node has countable level -/
  lvl_lt_omega1 : ∀ x, lvl x < omega1
  /-- the level function is strictly monotone -/
  lvl_strictMono : ∀ ⦃x y : T⦄, x < y → lvl x < lvl y
  /-- the predecessors of a node form a chain -/
  pred_chain : ∀ x : T, IsChain (· ≤ ·) {y | y < x}
  /-- a node has exactly one predecessor at each smaller level -/
  pred_unique : ∀ x : T, ∀ b < lvl x, ∃! y : T, y < x ∧ lvl y = b
  /-- the tree has height `ω₁` -/
  levels_nonempty : ∀ b < omega1, ∃ x : T, lvl x = b
  /-- all levels are countable -/
  levels_countable : ∀ b : Ordinal, {x : T | lvl x = b}.Countable
  /-- there is no uncountable chain -/
  chains_countable : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable

/-- In an Aronszajn tree the level function restricts to a bijection from the set of
predecessors of a node `x` onto `Set.Iio (lvl x)`; together with strict monotonicity of `lvl`
this says that the predecessors of `x` are order isomorphic to the ordinal `lvl x`. -/
