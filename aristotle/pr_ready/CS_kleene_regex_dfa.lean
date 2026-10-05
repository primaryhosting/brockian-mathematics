/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Statement: A language is regular iff it is accepted by a DFA (Kleene, finite direction).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
Antimirov partial derivatives: every language matched by a regular expression is regular
(i.e. accepted by a DFA with finitely many states).
-/

namespace CS

open RegularExpression Language Computability

universe u
variable {α : Type u}

/-! ### Membership lemmas for languages -/

theorem mem_mul_cons (L M : Language α) (a : α) (y : List α) :
    a :: y ∈ L * M ↔
      (∃ u v, u ++ v = y ∧ a :: u ∈ L ∧ v ∈ M) ∨ ([] ∈ L ∧ a :: y ∈ M) := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    cases u with
    | nil =>
      right
      simp only [List.nil_append] at huv
      exact ⟨hu, huv ▸ hv⟩
    | cons b u =>
      left
      simp only [List.cons_append, List.cons.injEq] at huv
      obtain ⟨rfl, rfl⟩ := huv
      exact ⟨u, v, rfl, hu, hv⟩
  · rintro (⟨u, v, rfl, hu, hv⟩ | ⟨h0, h⟩)
    · exact ⟨a :: u, hu, v, hv, rfl⟩
    · exact ⟨[], h0, a :: y, h, rfl⟩

theorem mem_kstar_cons (L : Language α) (a : α) (y : List α) :
    a :: y ∈ L∗ ↔ ∃ u v, u ++ v = y ∧ a :: u ∈ L ∧ v ∈ L∗ := by
  constructor
  · intro h
    rw [Language.mem_kstar_iff_exists_nonempty] at h
    obtain ⟨S, hS, hmem⟩ := h
    cases S with
    | nil => simp at hS
    | cons u S =>
      obtain ⟨hu, hune⟩ := hmem u (by simp)
      cases u with
      | nil => exact absurd rfl hune
      | cons b u =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, rfl⟩ := hS
        refine ⟨u, S.flatten, rfl, hu, ?_⟩
        exact Language.mem_kstar_iff_exists_nonempty.2 ⟨S, rfl, fun z hz => hmem z (by simp [hz])⟩
  · rintro ⟨u, v, rfl, hu, hv⟩
    have hmem : (a :: u) ++ v ∈ L * L∗ := ⟨a :: u, hu, v, hv, rfl⟩
    exact KleeneAlgebra.mul_kstar_le_kstar L hmem

theorem mem_matches'_zero (x : List α) : x ∈ (0 : RegularExpression α).matches' ↔ False := Iff.rfl

theorem mem_matches'_one (x : List α) : x ∈ (1 : RegularExpression α).matches' ↔ x = [] := Iff.rfl

theorem mem_matches'_char (b : α) (x : List α) : x ∈ (char b).matches' ↔ x = [b] := Iff.rfl

/-! ### Partial derivatives -/

variable [DecidableEq α]

/-- The Antimirov partial derivative of a regular expression with respect to a letter. -/
def pd : RegularExpression α → α → Set (RegularExpression α)
  | 0, _ => ∅
  | 1, _ => ∅
  | char b, a => if a = b then {1} else ∅
  | P + Q, a => pd P a ∪ pd Q a
  | P * Q, a => (fun p => p * Q) '' pd P a ∪ (if P.matchEpsilon then pd Q a else ∅)
  | RegularExpression.star P, a => (fun p => p * RegularExpression.star P) '' pd P a

@[simp] theorem pd_zero (a : α) : pd (0 : RegularExpression α) a = ∅ := rfl
@[simp] theorem pd_one (a : α) : pd (1 : RegularExpression α) a = ∅ := rfl
@[simp] theorem pd_char (a b : α) : pd (char b) a = if a = b then {1} else ∅ := rfl
@[simp] theorem pd_plus (P Q : RegularExpression α) (a : α) : pd (P + Q) a = pd P a ∪ pd Q a := rfl
@[simp] theorem pd_comp (P Q : RegularExpression α) (a : α) :
    pd (P * Q) a = (fun p => p * Q) '' pd P a ∪ (if P.matchEpsilon then pd Q a else ∅) := rfl
@[simp] theorem pd_star (P : RegularExpression α) (a : α) :
    pd (RegularExpression.star P) a = (fun p => p * RegularExpression.star P) '' pd P a := rfl

theorem nil_mem_matches'_iff (P : RegularExpression α) :
    [] ∈ P.matches' ↔ P.matchEpsilon = true := by
  rw [← P.rmatch_iff_matches' []]
  rfl

/-- Correctness of the partial derivative: the languages of the partial derivatives of `P`
with respect to `a` cover exactly the words `y` with `a :: y` matched by `P`. -/
theorem mem_pd_iff (P : RegularExpression α) (a : α) (y : List α) :
    (∃ p ∈ pd P a, y ∈ p.matches') ↔ a :: y ∈ P.matches' := by
  induction P generalizing y with
  | zero =>
      rw [RegularExpression.zero_def, pd_zero]
      simp
  | epsilon =>
      rw [RegularExpression.one_def, pd_one]
      simp
  | char b =>
      rw [pd_char, mem_matches'_char]
      by_cases h : a = b
      · subst h
        rw [if_pos rfl]
        constructor
        · rintro ⟨p, hp, hy⟩
          rw [Set.mem_singleton_iff] at hp
          subst hp
          rw [mem_matches'_one] at hy
          rw [hy]
        · intro hy
          rw [List.cons.injEq] at hy
          exact ⟨1, rfl, (mem_matches'_one y).2 hy.2⟩
      · rw [if_neg h]
        constructor
        · rintro ⟨p, hp, -⟩
          exact absurd hp (Set.notMem_empty p)
        · intro hy
          rw [List.cons.injEq] at hy
          exact absurd hy.1 h
  | plus P Q ihP ihQ =>
      rw [RegularExpression.plus_def, pd_plus]
      show (∃ p ∈ pd P a ∪ pd Q a, y ∈ p.matches') ↔ a :: y ∈ P.matches' + Q.matches'
      rw [show (a :: y ∈ P.matches' + Q.matches') ↔
          (a :: y ∈ P.matches' ∨ a :: y ∈ Q.matches') from Iff.rfl, ← ihP y, ← ihQ y]
      constructor
      · rintro ⟨p, hp | hp, hy⟩
        · exact Or.inl ⟨p, hp, hy⟩
        · exact Or.inr ⟨p, hp, hy⟩
      · rintro (⟨p, hp, hy⟩ | ⟨p, hp, hy⟩)
        · exact ⟨p, Or.inl hp, hy⟩
        · exact ⟨p, Or.inr hp, hy⟩
  | comp P Q ihP ihQ =>
      rw [RegularExpression.comp_def, pd_comp]
      show (∃ p ∈ (fun p => p * Q) '' pd P a ∪ (if P.matchEpsilon then pd Q a else ∅),
          y ∈ p.matches') ↔ a :: y ∈ P.matches' * Q.matches'
      rw [mem_mul_cons]
      constructor
      · rintro ⟨p, hp, hy⟩
        rcases hp with ⟨q, hq, rfl⟩ | hp
        · left
          obtain ⟨u, hu, v, hv, rfl⟩ := hy
          exact ⟨u, v, rfl, (ihP u).1 ⟨q, hq, hu⟩, hv⟩
        · right
          by_cases he : P.matchEpsilon = true
          · rw [if_pos he] at hp
            exact ⟨(nil_mem_matches'_iff P).2 he, (ihQ y).1 ⟨p, hp, hy⟩⟩
          · rw [if_neg he] at hp
            exact absurd hp (Set.notMem_empty p)
      · rintro (⟨u, v, rfl, hu, hv⟩ | ⟨h0, hy⟩)
        · obtain ⟨q, hq, hu⟩ := (ihP u).2 hu
          exact ⟨q * Q, Or.inl ⟨q, hq, rfl⟩, u, hu, v, hv, rfl⟩
        · obtain ⟨q, hq, hy⟩ := (ihQ y).2 hy
          have he : P.matchEpsilon = true := (nil_mem_matches'_iff P).1 h0
          exact ⟨q, Or.inr (by rw [if_pos he]; exact hq), hy⟩
  | star P ih =>
      rw [pd_star]
      show (∃ p ∈ (fun p => p * RegularExpression.star P) '' pd P a, y ∈ p.matches') ↔
        a :: y ∈ P.matches'∗
      rw [mem_kstar_cons]
      constructor
      · rintro ⟨p, ⟨q, hq, rfl⟩, hy⟩
        obtain ⟨u, hu, v, hv, rfl⟩ := hy
        exact ⟨u, v, rfl, (ih u).1 ⟨q, hq, hu⟩, hv⟩
      · rintro ⟨u, v, rfl, hu, hv⟩
        obtain ⟨q, hq, hu⟩ := (ih u).2 hu
        exact ⟨q * RegularExpression.star P, ⟨q, hq, rfl⟩, u, hu, v, hv, rfl⟩

/-- Partial derivatives with respect to a word. -/
def pds : RegularExpression α → List α → Set (RegularExpression α)
  | r, [] => {r}
  | r, a :: x => ⋃ p ∈ pd r a, pds p x

@[simp] theorem pds_nil (r : RegularExpression α) : pds r [] = {r} := rfl
@[simp] theorem pds_cons (r : RegularExpression α) (a : α) (x : List α) :
    pds r (a :: x) = ⋃ p ∈ pd r a, pds p x := rfl

theorem mem_pds_iff (x : List α) (P : RegularExpression α) (y : List α) :
    (∃ p ∈ pds P x, y ∈ p.matches') ↔ x ++ y ∈ P.matches' := by
  induction x generalizing P with
  | nil =>
      constructor
      · rintro ⟨p, hp, hy⟩
        rw [pds_nil, Set.mem_singleton_iff] at hp
        subst hp
        simpa using hy
      · intro hy
        exact ⟨P, by simp, by simpa using hy⟩
  | cons a x ih =>
      rw [pds_cons]
      rw [show (a :: x) ++ y = a :: (x ++ y) from rfl, ← mem_pd_iff P a (x ++ y)]
      constructor
      · rintro ⟨p, hp, hy⟩
        rw [Set.mem_iUnion₂] at hp
        obtain ⟨q, hq, hp⟩ := hp
        exact ⟨q, hq, (ih q).1 ⟨p, hp, hy⟩⟩
      · rintro ⟨q, hq, hy⟩
        obtain ⟨p, hp, hy⟩ := (ih q).2 hy
        exact ⟨p, Set.mem_iUnion₂.2 ⟨q, hq, hp⟩, hy⟩

/-! ### Finiteness -/

/-- An over-approximation of the set of all partial derivatives of a regular expression. -/
def PD : RegularExpression α → Set (RegularExpression α)
  | 0 => ∅
  | 1 => ∅
  | char _ => {1}
  | P + Q => PD P ∪ PD Q
  | P * Q => (fun p => p * Q) '' PD P ∪ PD Q
  | RegularExpression.star P => (fun p => p * RegularExpression.star P) '' PD P

omit [DecidableEq α] in
@[simp] theorem PD_zero : PD (0 : RegularExpression α) = ∅ := rfl
omit [DecidableEq α] in
@[simp] theorem PD_one : PD (1 : RegularExpression α) = ∅ := rfl
omit [DecidableEq α] in
@[simp] theorem PD_char (b : α) : PD (char b) = {1} := rfl
omit [DecidableEq α] in
@[simp] theorem PD_plus (P Q : RegularExpression α) : PD (P + Q) = PD P ∪ PD Q := rfl
omit [DecidableEq α] in
@[simp] theorem PD_comp (P Q : RegularExpression α) :
    PD (P * Q) = (fun p => p * Q) '' PD P ∪ PD Q := rfl
omit [DecidableEq α] in
@[simp] theorem PD_star (P : RegularExpression α) :
    PD (RegularExpression.star P) = (fun p => p * RegularExpression.star P) '' PD P := rfl

omit [DecidableEq α] in
theorem PD_finite (P : RegularExpression α) : (PD P).Finite := by
  induction P with
  | zero => rw [RegularExpression.zero_def, PD_zero]; exact Set.finite_empty
  | epsilon => rw [RegularExpression.one_def, PD_one]; exact Set.finite_empty
  | char b => rw [PD_char]; exact Set.finite_singleton _
  | plus P Q ihP ihQ => rw [RegularExpression.plus_def, PD_plus]; exact ihP.union ihQ
  | comp P Q ihP ihQ => rw [RegularExpression.comp_def, PD_comp]; exact (ihP.image _).union ihQ
  | star P ih => rw [PD_star]; exact ih.image _

theorem pd_subset_PD (P : RegularExpression α) (a : α) : pd P a ⊆ PD P := by
  induction P with
  | zero => rw [RegularExpression.zero_def, PD_zero, pd_zero]
  | epsilon => rw [RegularExpression.one_def, PD_one, pd_one]
  | char b =>
      rw [pd_char, PD_char]
      by_cases h : a = b
      · rw [if_pos h]
      · rw [if_neg h]; exact Set.empty_subset _
  | plus P Q ihP ihQ =>
      rw [RegularExpression.plus_def, PD_plus, pd_plus]
      exact Set.union_subset_union ihP ihQ
  | comp P Q ihP ihQ =>
      rw [RegularExpression.comp_def, PD_comp, pd_comp]
      refine Set.union_subset_union (Set.image_mono ihP) ?_
      by_cases he : P.matchEpsilon = true
      · rw [if_pos he]; exact ihQ
      · rw [if_neg he]; exact Set.empty_subset _
  | star P ih =>
      rw [PD_star, pd_star]
      exact Set.image_mono ih

theorem pd_of_mem_PD (P : RegularExpression α) (a : α) :
    ∀ p ∈ PD P, pd p a ⊆ PD P := by
  induction P with
  | zero =>
      intro p hp
      rw [RegularExpression.zero_def, PD_zero] at hp
      exact absurd hp (Set.notMem_empty p)
  | epsilon =>
      intro p hp
      rw [RegularExpression.one_def, PD_one] at hp
      exact absurd hp (Set.notMem_empty p)
  | char b =>
      intro p hp
      rw [PD_char, Set.mem_singleton_iff] at hp
      subst hp
      rw [pd_one]
      exact Set.empty_subset _
  | plus P Q ihP ihQ =>
      intro p hp
      rw [RegularExpression.plus_def, PD_plus] at hp ⊢
      rcases hp with hp | hp
      · exact (ihP p hp).trans Set.subset_union_left
      · exact (ihQ p hp).trans Set.subset_union_right
  | comp P Q ihP ihQ =>
      intro p hp
      rw [RegularExpression.comp_def, PD_comp] at hp ⊢
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · intro s hs
        rw [pd_comp] at hs
        rcases hs with ⟨t, ht, rfl⟩ | hs
        · exact Or.inl ⟨t, ihP q hq ht, rfl⟩
        · by_cases he : q.matchEpsilon = true
          · rw [if_pos he] at hs
            exact Or.inr (pd_subset_PD Q a hs)
          · rw [if_neg he] at hs
            exact absurd hs (Set.notMem_empty s)
      · exact (ihQ p hp).trans Set.subset_union_right
  | star P ih =>
      intro p hp
      rw [PD_star] at hp ⊢
      obtain ⟨q, hq, rfl⟩ := hp
      intro s hs
      rw [pd_comp] at hs
      rcases hs with ⟨t, ht, rfl⟩ | hs
      · exact ⟨t, ih q hq ht, rfl⟩
      · by_cases he : q.matchEpsilon = true
        · rw [if_pos he] at hs
          rw [pd_star] at hs
          exact Set.image_mono (pd_subset_PD P a) hs
        · rw [if_neg he] at hs
          exact absurd hs (Set.notMem_empty s)

theorem pds_subset (P : RegularExpression α) (x : List α) {q : RegularExpression α}
    (hq : q ∈ insert P (PD P)) : pds q x ⊆ insert P (PD P) := by
  induction x generalizing q with
  | nil => rw [pds_nil, Set.singleton_subset_iff]; exact hq
  | cons a x ih =>
      intro s hs
      rw [pds_cons, Set.mem_iUnion₂] at hs
      obtain ⟨p, hp, hs⟩ := hs
      have hpmem : p ∈ insert P (PD P) := by
        rcases hq with rfl | hq
        · exact Set.mem_insert_of_mem _ (pd_subset_PD q a hp)
        · exact Set.mem_insert_of_mem _ (pd_of_mem_PD P a q hq hp)
      exact ih hpmem hs

/-- The language of a set of regular expressions: the union of the languages they match. -/
def unionLang (S : Set (RegularExpression α)) : Language α := {y | ∃ p ∈ S, y ∈ p.matches'}

omit [DecidableEq α] in
theorem mem_unionLang {S : Set (RegularExpression α)} {x : List α} :
    x ∈ unionLang S ↔ ∃ p ∈ S, x ∈ p.matches' := Iff.rfl

theorem leftQuotient_matches' (P : RegularExpression α) (x : List α) :
    P.matches'.leftQuotient x = unionLang (pds P x) := by
  ext y
  rw [Language.mem_leftQuotient, mem_unionLang, mem_pds_iff]

/-- Every language matched by a regular expression is regular. -/
theorem isRegular_matches' (P : RegularExpression α) : P.matches'.IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient
  have hfin : (insert P (PD P)).Finite := (PD_finite P).insert P
  have hsub : Set.range P.matches'.leftQuotient ⊆
      unionLang '' {S | S ⊆ insert P (PD P)} := by
    rintro L ⟨x, rfl⟩
    exact ⟨pds P x, pds_subset P x (Set.mem_insert _ _), (leftQuotient_matches' P x).symm⟩
  exact Set.Finite.subset (Set.Finite.image _ hfin.finite_subsets) hsub

end CS


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

