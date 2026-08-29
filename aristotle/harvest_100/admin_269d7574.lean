import Mathlib
import RequestProject.Main

/-!
# Insertion sort correctness, stated with Mathlib's `List.Sorted`

`RequestProject/Main.lean` contains the target theorem `CS.insertion_sort_correct`
(it cannot contain an `import` line, since the mandated header comment must be the
first command of the file).  Here we restate it in Mathlib vocabulary, for a
`LinearOrder`, using `List.Pairwise (· ≤ ·)` (which is Mathlib's `List.Sorted (· ≤ ·)`).
-/

set_option autoImplicit false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- **Insertion sort is correct** (Mathlib phrasing): over a linear order,
`CS.insertionSort (· ≤ ·) l` is sorted (pairwise `≤`) and is a permutation of `l`. -/
theorem insertion_sort_correct_le (l : List α) :
    (insertionSort (· ≤ ·) l).Pairwise (· ≤ ·) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct (· ≤ ·) (fun a b => le_total a b)
    (fun _ _ _ h₁ h₂ => le_trans h₁ h₂) l

/-- Our insertion sort agrees with Mathlib's `List.insertionSort`. -/
theorem insertionSort_eq_list_insertionSort (l : List α) :
    insertionSort (· ≤ ·) l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [insertionSort_cons, ih, List.insertionSort_cons]
    generalize l.insertionSort (· ≤ ·) = m
    induction m with
    | nil => rfl
    | cons b m ihm =>
      by_cases h : a ≤ b <;> simp [orderedInsert_cons, h, ihm]

end CS

/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to come before any other
command, and a module docstring `/-! ... -/` counts as a command.  Since the header
comment above must be the very first thing in this file, no `import` line can follow it.
The development below is therefore written against the Lean 4 core library only
(`List.Perm`, `List.Pairwise`, which are the same notions Mathlib uses:
`List.Sorted r = List.Pairwise r`).
-/

set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} (le : α → α → Prop) [DecidableRel le]

/-- `orderedInsert le a l` inserts `a` into the list `l` just before the first element
`b` with `le a b`. -/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: orderedInsert a l

/-- `insertionSort le l` sorts `l` with respect to `le` using the insertion sort algorithm. -/
def insertionSort : List α → List α
  | [] => []
  | a :: l => orderedInsert le a (insertionSort l)

@[simp] theorem orderedInsert_nil (a : α) : orderedInsert le a ([] : List α) = [a] := rfl

@[simp] theorem orderedInsert_cons (a b : α) (l : List α) :
    orderedInsert le a (b :: l) =
      if le a b then a :: b :: l else b :: orderedInsert le a l := rfl

@[simp] theorem insertionSort_nil : insertionSort le ([] : List α) = [] := rfl

@[simp] theorem insertionSort_cons (a : α) (l : List α) :
    insertionSort le (a :: l) = orderedInsert le a (insertionSort le l) := rfl

/-- Inserting an element yields a permutation of the list with that element prepended. -/
theorem perm_orderedInsert (a : α) : ∀ l : List α, (orderedInsert le a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    by_cases h : le a b
    · simp [h]
    · have : ((b :: orderedInsert le a l) : List α).Perm (b :: a :: l) :=
        (perm_orderedInsert a l).cons b
      simpa [h] using this.trans (List.Perm.swap a b l)

/-- Inserting into a sorted list keeps it sorted. -/
theorem pairwise_orderedInsert (htotal : ∀ a b : α, le a b ∨ le b a)
    (htrans : ∀ a b c : α, le a b → le b c → le a c) (a : α) :
    ∀ l : List α, l.Pairwise le → (orderedInsert le a l).Pairwise le
  | [], _ => List.pairwise_singleton le a
  | b :: l, hl => by
    rw [List.pairwise_cons] at hl
    by_cases h : le a b
    · rw [orderedInsert_cons, if_pos h, List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.2 hl⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact htrans _ _ _ h (hl.1 c hc)
    · rw [orderedInsert_cons, if_neg h, List.pairwise_cons]
      refine ⟨?_, pairwise_orderedInsert htotal htrans a l hl.2⟩
      intro c hc
      have hc' := (perm_orderedInsert le a l).mem_iff.1 hc
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact (htotal _ _).resolve_left h
      · exact hl.1 c hc'

/-- `insertionSort` returns a permutation of its input. -/
theorem perm_insertionSort : ∀ l : List α, (insertionSort le l).Perm l
  | [] => List.Perm.refl _
  | a :: l => by
    simpa using (perm_orderedInsert le a (insertionSort le l)).trans
      ((perm_insertionSort l).cons a)

/-- `insertionSort` returns a sorted list. -/
theorem pairwise_insertionSort (htotal : ∀ a b : α, le a b ∨ le b a)
    (htrans : ∀ a b c : α, le a b → le b c → le a c) :
    ∀ l : List α, (insertionSort le l).Pairwise le
  | [] => List.Pairwise.nil
  | a :: l => pairwise_orderedInsert le htotal htrans a _ (pairwise_insertionSort htotal htrans l)

/-- **Insertion sort is correct**: for a total, transitive (decidable) relation `le`,
`insertionSort le l` is sorted with respect to `le` and is a permutation of `l`. -/
theorem insertion_sort_correct (htotal : ∀ a b : α, le a b ∨ le b a)
    (htrans : ∀ a b c : α, le a b → le b c → le a c) (l : List α) :
    (insertionSort le l).Pairwise le ∧ (insertionSort le l).Perm l :=
  ⟨pairwise_insertionSort le htotal htrans l, perm_insertionSort le l⟩

/-- Specialisation to natural numbers with `≤`. -/
theorem insertion_sort_correct_nat (l : List Nat) :
    (insertionSort (· ≤ ·) l).Pairwise (· ≤ ·) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct _ (fun a b => Nat.le_total a b) (fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂) l

end CS

