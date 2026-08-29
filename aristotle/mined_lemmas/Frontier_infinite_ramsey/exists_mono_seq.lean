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
