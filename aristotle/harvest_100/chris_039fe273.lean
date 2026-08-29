/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace CS

/-- `orderedInsert r a l` inserts `a` into `l` in front of the first element
`b` of `l` with `r a b`. -/
def orderedInsert {α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) :
    List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert r a l

/-- Insertion sort with respect to the relation `r`. -/
def insertionSort {α : Type u} (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | a :: l => orderedInsert r a (insertionSort r l)

/-- A list is sorted for `r` when every element is related to all later ones. -/
abbrev Sorted {α : Type u} (r : α → α → Prop) (l : List α) : Prop := List.Pairwise r l

section

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

@[simp]
theorem orderedInsert_nil (a : α) : orderedInsert r a ([] : List α) = [a] := rfl

theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: orderedInsert r a l := rfl

@[simp]
theorem insertionSort_nil : insertionSort r ([] : List α) = [] := rfl

@[simp]
theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort r (a :: l) = orderedInsert r a (insertionSort r l) := rfl

/-- `orderedInsert r a l` is a permutation of `a :: l`. -/
theorem orderedInsert_perm (a : α) : ∀ l : List α, (orderedInsert r a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
      rw [orderedInsert_cons]
      split
      · exact List.Perm.refl _
      · exact ((orderedInsert_perm a l).cons b).trans (List.Perm.swap a b l)

/-- Membership in `orderedInsert r a l`. -/
theorem mem_orderedInsert {a b : α} {l : List α} :
    b ∈ orderedInsert r a l ↔ b = a ∨ b ∈ l := by
  have h := (orderedInsert_perm r a l).mem_iff (a := b)
  simpa using h

/-- Inserting into a sorted list keeps it sorted, provided `r` is total and transitive. -/
theorem sorted_orderedInsert (htotal : ∀ x y : α, r x y ∨ r y x)
    (htrans : ∀ x y z : α, r x y → r y z → r x z) (a : α) :
    ∀ l : List α, Sorted r l → Sorted r (orderedInsert r a l)
  | [], _ => List.pairwise_singleton r a
  | b :: l, hl => by
      obtain ⟨hb, hls⟩ := List.pairwise_cons.mp hl
      rw [orderedInsert_cons]
      split
      · rename_i hab
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hab
          · exact htrans _ _ _ hab (hb c hc)
        · exact List.pairwise_cons.mpr ⟨hb, hls⟩
      · rename_i hab
        have hba : r b a := (htotal a b).resolve_left hab
        refine List.pairwise_cons.mpr ⟨?_, sorted_orderedInsert htotal htrans a l hls⟩
        intro c hc
        rcases (mem_orderedInsert r).mp hc with rfl | hc
        · exact hba
        · exact hb c hc

/-- `insertionSort` returns a permutation of its input. -/
theorem insertionSort_perm : ∀ l : List α, (insertionSort r l).Perm l
  | [] => List.Perm.refl _
  | a :: l => by
      rw [insertionSort_cons]
      exact (orderedInsert_perm r a (insertionSort r l)).trans ((insertionSort_perm l).cons a)

/-- `insertionSort` returns a sorted list, provided `r` is total and transitive. -/
theorem sorted_insertionSort (htotal : ∀ x y : α, r x y ∨ r y x)
    (htrans : ∀ x y z : α, r x y → r y z → r x z) :
    ∀ l : List α, Sorted r (insertionSort r l)
  | [] => List.Pairwise.nil
  | a :: l => sorted_orderedInsert r htotal htrans a _ (sorted_insertionSort htotal htrans l)

/-- **Insertion sort is correct**: for a total, transitive relation `r`,
`insertionSort r l` is a sorted permutation of `l`. -/
theorem insertion_sort_correct (htotal : ∀ x y : α, r x y ∨ r y x)
    (htrans : ∀ x y z : α, r x y → r y z → r x z) (l : List α) :
    Sorted r (insertionSort r l) ∧ (insertionSort r l).Perm l :=
  ⟨sorted_insertionSort r htotal htrans l, insertionSort_perm r l⟩

end

/-- Specialization to `≤` on the natural numbers. -/
theorem insertion_sort_correct_nat (l : List Nat) :
    Sorted (· ≤ ·) (insertionSort (· ≤ ·) l) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct (· ≤ ·) (fun x y => Nat.le_total x y)
    (fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂) l

end CS

