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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Set disjointness has `Ω(n)` randomized communication complexity

We formalise two-party communication protocols as decision trees (`CS.Protocol`), where
`CS.Protocol.cost` is the depth of the tree, i.e. the worst-case number of bits exchanged.

A *public-coin randomized protocol* is modelled as a finite family `P : Fin m → Protocol X Y`
of deterministic protocols, run under the uniform distribution on `Fin m` (allowing repetitions
in the family, this captures every distribution with rational probabilities).

The main theorem `CS.disjointness_lb` states the `Ω(n)` lower bound for randomized protocols
with *one-sided error* (false-biased protocols): if every protocol in the family is sound
(it never accepts a pair of intersecting sets) and, for every disjoint pair, at least half of
the protocols accept, then some protocol in the family has cost at least `n - 1`.

The engine is the classical fooling-set bound `CS.Protocol.fooling_card_le`, proved by
induction on the protocol tree, together with a double counting argument over the fooling set
`{ (x, xᶜ) : x ∈ {0,1}ⁿ }` of size `2ⁿ`.
-/

namespace CS

variable {X Y : Type*}

/-- A deterministic two-party communication protocol, as a decision tree.
`nodeA g t0 t1` means Alice sends the bit `g x` and the protocol continues in `t1` (if the bit
is `true`) or `t0` (if it is `false`); `nodeB` is the same with Bob speaking. -/
inductive Protocol (X Y : Type*) : Type _
  | leaf : Bool → Protocol X Y
  | nodeA : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | nodeB : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number of
bits exchanged. -/

theorem Protocol.fooling_card_le (f : X → Y → Bool) :
    ∀ (P : Protocol X Y) (A : Set X) (B : Set Y) (F : Finset (X × Y)),
      (∀ x ∈ A, ∀ y ∈ B, P.run x y = true → f x y = true) →
      (∀ p ∈ F, p.1 ∈ A ∧ p.2 ∈ B ∧ P.run p.1 p.2 = true) →
      IsFooling f F → F.card ≤ 2 ^ P.cost := by
  intro P
  induction P with
  | leaf b =>
      intro A B F hsound hmem hfool
      cases b with
      | false =>
          have hF : F = ∅ := by
            refine Finset.eq_empty_iff_forall_notMem.mpr ?_
            intro p hp
            have h := (hmem p hp).2.2
            simp [Protocol.run] at h
          simp [hF]
      | true =>
          have hcard : F.card ≤ 1 := by
            refine Finset.card_le_one.mpr ?_
            intro p hp q hq
            by_contra hne
            rcases hfool p hp q hq hne with h | h
            · have := hsound p.1 (hmem p hp).1 q.2 (hmem q hq).2.1 (by simp [Protocol.run])
              simp [this] at h
            · have := hsound q.1 (hmem q hq).1 p.2 (hmem p hp).2.1 (by simp [Protocol.run])
              simp [this] at h
          calc F.card ≤ 1 := hcard
            _ ≤ 2 ^ (Protocol.leaf (X := X) (Y := Y) true).cost := by
                simp [Protocol.cost]
  | nodeA g t0 t1 ih0 ih1 =>
      intro A B F hsound hmem hfool
      classical
      have hsub : ∀ (F' : Finset (X × Y)), F' ⊆ F → IsFooling f F' := by
        intro F' hF' p hp q hq hne
        exact hfool p (hF' hp) q (hF' hq) hne
      have h1 : (F.filter (fun p => g p.1 = true)).card ≤ 2 ^ t1.cost := by
        refine ih1 (A ∩ {x | g x = true}) B _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          have hgx : g x = true := hx.2
          exact hsound x hx.1 y hy (by rw [Protocol.run, if_pos hgx]; exact hrun)
        · intro p hp
          rw [Finset.mem_filter] at hp
          refine ⟨⟨(hmem p hp.1).1, hp.2⟩, (hmem p hp.1).2.1, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_pos hp.2] at this
          exact this
      have h0 : (F.filter (fun p => ¬ (g p.1 = true))).card ≤ 2 ^ t0.cost := by
        refine ih0 (A ∩ {x | g x = false}) B _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          refine hsound x hx.1 y hy ?_
          have : g x = false := hx.2
          simp [Protocol.run, this, hrun]
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hg : g p.1 = false := by simpa using hp.2
          refine ⟨⟨(hmem p hp.1).1, hg⟩, (hmem p hp.1).2.1, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_neg (by simp [hg])] at this
          exact this
      have hsplit : (F.filter (fun p => g p.1 = true)).card
          + (F.filter (fun p => ¬ (g p.1 = true))).card = F.card :=
        Finset.card_filter_add_card_filter_not _
      have hmax0 : (2 : ℕ) ^ t0.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hmax1 : (2 : ℕ) ^ t1.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : F.card ≤ 2 ^ max t0.cost t1.cost + 2 ^ max t0.cost t1.cost := by
        rw [← hsplit]
        exact Nat.add_le_add (h1.trans hmax1) (h0.trans hmax0)
      simpa [Protocol.cost, two_mul, pow_succ, mul_comm] using this
  | nodeB g t0 t1 ih0 ih1 =>
      intro A B F hsound hmem hfool
      classical
      have hsub : ∀ (F' : Finset (X × Y)), F' ⊆ F → IsFooling f F' := by
        intro F' hF' p hp q hq hne
        exact hfool p (hF' hp) q (hF' hq) hne
      have h1 : (F.filter (fun p => g p.2 = true)).card ≤ 2 ^ t1.cost := by
        refine ih1 A (B ∩ {y | g y = true}) _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          have hgy : g y = true := hy.2
          exact hsound x hx y hy.1 (by rw [Protocol.run, if_pos hgy]; exact hrun)
        · intro p hp
          rw [Finset.mem_filter] at hp
          refine ⟨(hmem p hp.1).1, ⟨(hmem p hp.1).2.1, hp.2⟩, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_pos hp.2] at this
          exact this
      have h0 : (F.filter (fun p => ¬ (g p.2 = true))).card ≤ 2 ^ t0.cost := by
        refine ih0 A (B ∩ {y | g y = false}) _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          refine hsound x hx y hy.1 ?_
          have : g y = false := hy.2
          simp [Protocol.run, this, hrun]
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hg : g p.2 = false := by simpa using hp.2
          refine ⟨(hmem p hp.1).1, ⟨(hmem p hp.1).2.1, hg⟩, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_neg (by simp [hg])] at this
          exact this
      have hsplit : (F.filter (fun p => g p.2 = true)).card
          + (F.filter (fun p => ¬ (g p.2 = true))).card = F.card :=
        Finset.card_filter_add_card_filter_not _
      have hmax0 : (2 : ℕ) ^ t0.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hmax1 : (2 : ℕ) ^ t1.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : F.card ≤ 2 ^ max t0.cost t1.cost + 2 ^ max t0.cost t1.cost := by
        rw [← hsplit]
        exact Nat.add_le_add (h1.trans hmax1) (h0.trans hmax0)
      simpa [Protocol.cost, two_mul, pow_succ, mul_comm] using this

/-- The set-disjointness function on subsets of `Fin n`, encoded as characteristic vectors. -/
