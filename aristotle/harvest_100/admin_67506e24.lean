import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Filter Set

open Classical in
/-- Choice of an element of a set of naturals (junk value `0` when empty). -/
noncomputable def pickElem (s : Set ℕ) : ℕ := if h : s.Nonempty then h.choose else 0

theorem pickElem_mem {s : Set ℕ} (h : s.Nonempty) : pickElem s ∈ s := by
  simp only [pickElem, dif_pos h]
  exact h.choose_spec

/-- The decreasing family of sets used to build a monochromatic sequence. -/
noncomputable def ramseySets (g : ℕ → ℕ → Bool) (c : Bool) (A : Set ℕ) : ℕ → Set ℕ
  | 0 => A
  | k + 1 =>
      {m ∈ ramseySets g c A k |
        pickElem (ramseySets g c A k) < m ∧ g (pickElem (ramseySets g c A k)) m = c}

/-- The monochromatic sequence itself. -/
noncomputable def ramseySeq (g : ℕ → ℕ → Bool) (c : Bool) (A : Set ℕ) (k : ℕ) : ℕ :=
  pickElem (ramseySets g c A k)

/-- Key lemma: for any colouring `g` of ordered pairs there is a strictly increasing sequence
all of whose (increasing) pairs get the same colour. -/
theorem exists_mono_seq (g : ℕ → ℕ → Bool) :
    ∃ (a : ℕ → ℕ) (c : Bool), StrictMono a ∧ ∀ i j, i < j → g (a i) (a j) = c := by
  classical
  set U : Ultrafilter ℕ := hyperfilter ℕ with hU
  -- each `n` has a colour that is `U`-large
  have hcol : ∀ n : ℕ, ∃ b : Bool, {m | g n m = b} ∈ U := by
    intro n
    have huniv : {m | g n m = true} ∪ {m | g n m = false} = Set.univ := by
      ext m; cases g n m <;> simp
    have : {m | g n m = true} ∪ {m | g n m = false} ∈ U := by
      rw [huniv]; exact Filter.univ_mem
    rcases (Ultrafilter.union_mem_iff).1 this with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  choose col hcolmem using hcol
  -- one colour class of `col` is `U`-large
  have hc : ∃ c : Bool, {n | col n = c} ∈ U := by
    have huniv : {n | col n = true} ∪ {n | col n = false} = Set.univ := by
      ext m; cases col m <;> simp
    have : {n | col n = true} ∪ {n | col n = false} ∈ U := by
      rw [huniv]; exact Filter.univ_mem
    rcases (Ultrafilter.union_mem_iff).1 this with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨c, hcU⟩ := hc
  set A : Set ℕ := {n | col n = c} with hA
  set F : ℕ → Set ℕ := ramseySets g c A with hF
  set a : ℕ → ℕ := ramseySeq g c A with ha
  have hFsucc : ∀ k, F (k + 1) = {m ∈ F k | a k < m ∧ g (a k) m = c} := by
    intro k; rfl
  have hasub : ∀ k, F (k + 1) ⊆ F k := by
    intro k m hm
    rw [hFsucc] at hm
    exact hm.1
  have hgt : ∀ x : ℕ, {m : ℕ | x < m} ∈ U := by
    intro x
    apply Filter.mem_hyperfilter_of_finite_compl
    have : {m : ℕ | x < m}ᶜ ⊆ Set.Iic x := by
      intro m hm; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hm
      exact hm
    exact (Set.finite_Iic x).subset this
  have hmemU : ∀ k, F k ∈ U := by
    intro k
    induction k with
    | zero => exact hcU
    | succ k ih =>
        have hak : a k ∈ F k := pickElem_mem (Ultrafilter.nonempty_of_mem ih)
        have hakA : a k ∈ A := by
          have hsub : ∀ j, F j ⊆ A := by
            intro j
            induction j with
            | zero => exact fun m hm => hm
            | succ j ihj => exact fun m hm => ihj (hasub j hm)
          exact hsub k hak
        have hcolak : col (a k) = c := hakA
        have h1 : {m | g (a k) m = c} ∈ U := by
          have := hcolmem (a k); rw [hcolak] at this; exact this
        rw [hFsucc]
        have : {m ∈ F k | a k < m ∧ g (a k) m = c}
            = F k ∩ ({m : ℕ | a k < m} ∩ {m | g (a k) m = c}) := by
          ext m; exact Iff.rfl
        rw [this]
        exact Filter.inter_mem ih (Filter.inter_mem (hgt (a k)) h1)
  have hamem : ∀ k, a k ∈ F k := fun k => pickElem_mem (Ultrafilter.nonempty_of_mem (hmemU k))
  have hmono : ∀ k j, k < j → F j ⊆ F (k + 1) := by
    intro k j hkj
    induction j with
    | zero => omega
    | succ j ihj =>
        rcases Nat.lt_or_ge k j with h | h
        · exact (hasub j).trans (ihj h)
        · have : k = j := by omega
          subst this; exact fun m hm => hm
  have hstep : ∀ i j, i < j → a i < a j ∧ g (a i) (a j) = c := by
    intro i j hij
    have : a j ∈ F (i + 1) := hmono i j hij (hamem j)
    rw [hFsucc] at this
    exact ⟨this.2.1, this.2.2⟩
  refine ⟨a, c, ?_, fun i j hij => (hstep i j hij).2⟩
  intro i j hij
  exact (hstep i j hij).1

/-- **Infinite Ramsey theorem** (for pairs, two colours): every 2-colouring of the
two-element subsets of `ℕ` admits an infinite monochromatic set. -/
theorem infinite_ramsey (f : Finset ℕ → Bool) :
    ∃ (S : Set ℕ) (c : Bool), S.Infinite ∧
      ∀ e : Finset ℕ, ↑e ⊆ S → e.card = 2 → f e = c := by
  obtain ⟨a, c, hmonoa, hcol⟩ := exists_mono_seq (fun x y => f {x, y})
  refine ⟨Set.range a, c, Set.infinite_range_of_injective hmonoa.injective, ?_⟩
  intro e he hcard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
  obtain ⟨i, rfl⟩ : ∃ i, a i = x := by
    have : x ∈ Set.range a := he (by simp)
    exact this
  obtain ⟨j, rfl⟩ : ∃ j, a j = y := by
    have : y ∈ Set.range a := he (by simp)
    exact this
  rcases lt_trichotomy i j with h | h | h
  · exact hcol i j h
  · exact absurd (congrArg a h) hxy
  · have := hcol j i h
    simpa [Finset.pair_comm] using this

end Frontier

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

