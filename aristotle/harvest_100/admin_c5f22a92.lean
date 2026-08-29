import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A two-valued splitting lemma: if a set is infinite, one of the two colour classes
determined by a `Bool`-valued function is infinite. -/
lemma infinite_of_bool_split (T : Set ℕ) (g : ℕ → Bool) (hT : T.Infinite) :
    {n | n ∈ T ∧ g n = true}.Infinite ∨ {n | n ∈ T ∧ g n = false}.Infinite := by
  by_contra h
  push_neg at h
  refine hT (((h.1).union h.2).subset ?_)
  intro n hn
  cases hb : g n
  · exact Or.inr ⟨hn, hb⟩
  · exact Or.inl ⟨hn, hb⟩

/-- The set of elements of `S` above its least element is infinite when `S` is. -/
lemma infinite_tail {S : Set ℕ} (hS : S.Infinite) (a : ℕ) :
    {n | n ∈ S ∧ a < n}.Infinite := by
  have h : {n | n ∈ S ∧ a < n} = S \ Set.Iic a := by
    ext n; simp [Set.mem_Iic, and_comm, not_le]
  rw [h]
  exact hS.diff (Set.finite_Iic a)

variable (c : ℕ → ℕ → Bool)

/-- The colour that occurs infinitely often from the least element of `S` to `S`. -/
noncomputable def col (S : Set ℕ) : Bool :=
  if {n | n ∈ S ∧ sInf S < n ∧ c (sInf S) n = true}.Infinite then true else false

/-- The infinite subset of `S` on which the least element of `S` has constant colour. -/
noncomputable def nextSet (S : Set ℕ) : Set ℕ :=
  {n | n ∈ S ∧ sInf S < n ∧ c (sInf S) n = col c S}

lemma nextSet_subset (S : Set ℕ) : nextSet c S ⊆ S := fun _ hn => hn.1

lemma lt_of_mem_nextSet {S : Set ℕ} {n : ℕ} (hn : n ∈ nextSet c S) : sInf S < n := hn.2.1

lemma col_of_mem_nextSet {S : Set ℕ} {n : ℕ} (hn : n ∈ nextSet c S) :
    c (sInf S) n = col c S := hn.2.2

lemma nextSet_infinite {S : Set ℕ} (hS : S.Infinite) : (nextSet c S).Infinite := by
  by_cases h : {n | n ∈ S ∧ sInf S < n ∧ c (sInf S) n = true}.Infinite
  · have hcol : col c S = true := by simp only [col]; exact if_pos h
    have hEq : nextSet c S = {n | n ∈ S ∧ sInf S < n ∧ c (sInf S) n = true} := by
      simp only [nextSet, hcol]
    rw [hEq]
    exact h
  · have hcol : col c S = false := by simp only [col]; exact if_neg h
    have hsplit := infinite_of_bool_split {n | n ∈ S ∧ sInf S < n} (fun n => c (sInf S) n)
      (infinite_tail hS (sInf S))
    have hfalse : {n | (n ∈ S ∧ sInf S < n) ∧ c (sInf S) n = false}.Infinite := by
      rcases hsplit with h1 | h2
      · refine absurd ?_ h
        refine h1.mono ?_
        rintro n ⟨⟨hnS, hlt⟩, hc⟩
        exact ⟨hnS, hlt, hc⟩
      · exact h2
    refine hfalse.mono ?_
    rintro n ⟨⟨hnS, hlt⟩, hc⟩
    exact (⟨hnS, hlt, by rw [hc, hcol]⟩ : n ∈ nextSet c S)

/-- The recursively constructed decreasing chain of infinite sets. -/
noncomputable def seqSet : ℕ → Set ℕ
  | 0 => Set.univ
  | (k + 1) => nextSet c (seqSet k)

lemma seqSet_infinite : ∀ k, (seqSet c k).Infinite
  | 0 => Set.infinite_univ
  | (k + 1) => nextSet_infinite c (seqSet_infinite k)

lemma seqSet_succ_subset (k : ℕ) : seqSet c (k + 1) ⊆ seqSet c k :=
  nextSet_subset c _

lemma seqSet_antitone {k l : ℕ} (h : k ≤ l) : seqSet c l ⊆ seqSet c k := by
  induction l with
  | zero => simpa using (Nat.le_zero.mp h) ▸ subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · exact (seqSet_succ_subset c n).trans (ih (Nat.lt_succ_iff.mp hk))
    · have : k = n + 1 := le_antisymm h hk
      subst this
      exact subset_rfl

/-- The increasing sequence of chosen elements. -/
noncomputable def elt (k : ℕ) : ℕ := sInf (seqSet c k)

lemma elt_mem (k : ℕ) : elt c k ∈ seqSet c k :=
  Nat.sInf_mem (seqSet_infinite c k).nonempty

lemma elt_lt {k l : ℕ} (h : k < l) : elt c k < elt c l := by
  have hmem : elt c l ∈ seqSet c (k + 1) := seqSet_antitone c h (elt_mem c l)
  exact lt_of_mem_nextSet c hmem

lemma elt_strictMono : StrictMono (elt c) := fun _ _ h => elt_lt c h

lemma elt_color {k l : ℕ} (h : k < l) : c (elt c k) (elt c l) = col c (seqSet c k) := by
  have hmem : elt c l ∈ seqSet c (k + 1) := seqSet_antitone c h (elt_mem c l)
  exact col_of_mem_nextSet c hmem

lemma exists_infinite_color (g : ℕ → Bool) : ∃ b : Bool, {k | g k = b}.Infinite := by
  by_contra h
  push_neg at h
  refine Set.infinite_univ (α := ℕ) (((h true).union (h false)).subset ?_)
  intro n _
  cases hb : g n
  · exact Or.inr hb
  · exact Or.inl hb

/-- **Infinite Ramsey theorem for pairs and two colours.**
Every 2-colouring `c` of the unordered pairs of natural numbers (encoded as `c x y` for
`x < y`) admits an infinite set `S` all of whose pairs receive the same colour `b`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (b : Bool), S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → c x y = b := by
  obtain ⟨b, hb⟩ := exists_infinite_color (fun k => col c (seqSet c k))
  refine ⟨elt c '' {k | col c (seqSet c k) = b}, b, hb.image ((elt_strictMono c).injective.injOn),
    ?_⟩
  rintro x ⟨k, hk, rfl⟩ y ⟨l, hl, rfl⟩ hxy
  have hkl : k < l := (elt_strictMono c).lt_iff_lt.mp hxy
  rw [elt_color c hkl]
  exact hk

end Frontier

