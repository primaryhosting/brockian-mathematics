import Mathlib

namespace Brockian.Cayley

open Finset

/-!
# Cayley's formula

The number of labeled trees on `n` vertices is `n ^ (n - 2)`.

The proof goes through *rooted forests*, encoded as "parent functions": a rooted forest on a
vertex set `A` with set of roots `S ⊆ A` is a function `f : V → V` which fixes everything
outside `A \ S`, maps `A \ S` into `A`, and such that iterating `f` from any vertex of `A`
eventually lands in `S`.

The main counting statement is
`|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)`,
proved by induction on `|A|` (deleting a root and summing over the set of its children).

Specialising to `A = univ` and `S = {0}` in `Fin n` and putting rooted forests with a single
root in bijection with trees gives Cayley's formula.
-/

/-! ### Rooted forests, encoded by parent functions -/

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsForest A S f` says that `f` is the parent function of a rooted forest on the vertex
set `A` whose set of roots is `S`. -/
structure IsForest (A S : Finset V) (f : V → V) : Prop where
  /-- Vertices which are not non-root vertices of the forest are fixed. -/
  fixed : ∀ v, v ∉ A \ S → f v = v
  /-- The parent of a non-root vertex is a vertex. -/
  maps : ∀ v ∈ A \ S, f v ∈ A
  /-- Iterating the parent function eventually reaches a root. -/
  reaches : ∀ v ∈ A, ∃ m, f^[m] v ∈ S

/-- The finset of rooted forests on `A` with roots `S`, encoded by parent functions. -/

lemma card_forestFinset_aux : ∀ (n : ℕ) (A S : Finset V), A.card = n → S ⊆ A →
    A.card * (forestFinset A S).card = S.card * A.card ^ (A.card - S.card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A S hA hSA
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rcases A.eq_empty_or_nonempty with rfl | hA'
    · simp
    · rw [forestFinset_empty_roots hA']
      simp
  · by_cases hAS : S = A
    · subst hAS
      rw [forestFinset_self]
      simp
    · obtain ⟨r, hr⟩ := hS
      have hrA : r ∈ A := hSA hr
      have hlt : S.card < A.card := Finset.card_lt_card (lt_of_le_of_ne hSA hAS)
      obtain ⟨j, hj⟩ : ∃ j, S.card = j + 1 :=
        ⟨S.card - 1, by have := Finset.card_pos.mpr ⟨r, hr⟩; omega⟩
      set m := (A \ S).card with hm
      have hmA : A.card = j + 1 + m := by
        have := Finset.card_sdiff_add_card_eq_card hSA
        omega
      have hm1 : 1 ≤ m := by omega
      have hAe : (A.erase r).card = j + m := by
        rw [Finset.card_erase_of_mem hrA, hmA]; omega
      have key : (j + m) * (forestFinset A S).card
          = ∑ C ∈ (A \ S).powerset, ((j + C.card) * (j + m) ^ (m - C.card)) := by
        rw [card_forestFinset_split hr hSA, Finset.mul_sum]
        refine Finset.sum_congr rfl fun C hC => ?_
        have hCA : C ⊆ A \ S := Finset.mem_powerset.mp hC
        have hCcard : C.card ≤ m := hm ▸ Finset.card_le_card hCA
        have hdisj : Disjoint (S.erase r) C := by
          refine Finset.disjoint_left.2 fun a ha haC => ?_
          exact (Finset.mem_sdiff.mp (hCA haC)).2 (Finset.mem_of_mem_erase ha)
        have hsub : S.erase r ∪ C ⊆ A.erase r := by
          refine Finset.union_subset (Finset.erase_subset_erase _ hSA) fun a ha => ?_
          have ha' := Finset.mem_sdiff.mp (hCA ha)
          exact Finset.mem_erase.2 ⟨fun h => ha'.2 (h ▸ hr), ha'.1⟩
        have hcards : (S.erase r ∪ C).card = j + C.card := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hr, hj]
          omega
        have h := ih (A.erase r).card (by omega) (A.erase r) (S.erase r ∪ C) rfl hsub
        rw [hAe, hcards] at h
        rw [h]
        congr 2
        omega
      rw [Finset.sum_powerset_apply_card (fun i => (j + i) * (j + m) ^ (m - i))] at key
      simp only [smul_eq_mul, ← hm] at key
      have main := sum_binom_aux j m
      rw [← key] at main
      have h2 : (j + m) * ((j + 1 + m) * (forestFinset A S).card)
          = (j + m) * ((j + 1) * (j + 1 + m) ^ m) := by
        calc (j + m) * ((j + 1 + m) * (forestFinset A S).card)
            = (j + 1 + m) * ((j + m) * (forestFinset A S).card) := by ring
          _ = (j + 1) * ((j + m) * (j + 1 + m) ^ m) := main
          _ = (j + m) * ((j + 1) * (j + 1 + m) ^ m) := by ring
      have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < j + m) h2
      rw [hmA, hj, show j + 1 + m - (j + 1) = m by omega]
      exact h3

/-- **The number of rooted forests.** -/
