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
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem exists_limit_step {a : Ordinal.{0}} (ha : a < ω₁) (ha0 : 0 < a)
    (halim : ∀ b < a, b + 1 < a) {d : Ordinal.{0} → Ordinal.{0} → ℕ}
    (hd : ∀ b < a, Nice b (d b) ∧ ∀ c < b, Coh (d b) (d c) c) :
    ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b := by
  classical
  obtain ⟨seq, hseq0, hseqlt, hseqmono, hseqcof⟩ := exists_cofinal_seq ha ha0 halim
  set St := (Ordinal.{0} → ℕ) × Finset ℕ with hSt
  set Q : ℕ → St → Prop := fun n s =>
    Nice (seq n) s.1 ∧ (∀ b ≤ seq n, Coh s.1 (d b) b) ∧ s.2.card = n ∧
      (∀ x ∈ s.2, ∀ e < seq n, s.1 e ≠ x) with hQdef
  -- the initial stage
  have hs0 : Q 0 ((fun _ => 0 : Ordinal.{0} → ℕ), (∅ : Finset ℕ)) := by
    refine ⟨by rw [hseq0]; exact nice_zero, ?_, rfl, by simp⟩
    intro b hb
    rw [hseq0] at hb
    have : b = 0 := le_antisymm hb (by simp)
    subst this
    exact coh_of_eq fun e he => absurd he (by simp)
  -- the recursion step
  have hstep : ∀ (n : ℕ) (s : St), Q n s →
      ∃ s' : St, Q (n + 1) s' ∧ s.2 ⊆ s'.2 ∧ ∀ e < seq n, s'.1 e = s.1 e := by
    intro n s hs
    obtain ⟨hnice, hcohs, hcard, havoid⟩ := hs
    have hlt : seq n < seq (n + 1) := hseqmono (Nat.lt_succ_self n)
    -- a fresh reserved value
    obtain ⟨r, hr1, hr2⟩ := (hnice.2.2.diff s.2.finite_toSet).nonempty
    have hcoh1 : Coh s.1 (d (seq (n + 1))) (seq n) :=
      (hcohs (seq n) le_rfl).trans
        (((hd (seq (n + 1)) (hseqlt _)).2 (seq n) hlt).symm)
    have hS : ∀ e < seq n, s.1 e ∉ ((insert r s.2 : Finset ℕ) : Set ℕ) := by
      intro e he hmem
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hmem
      rcases hmem with h | h
      · exact hr1 e he h
      · exact havoid _ h e he rfl
    obtain ⟨f', hf'nice, hf'agree, hf'coh, hf'avoid⟩ :=
      exists_extend hlt.le hnice (hd (seq (n + 1)) (hseqlt _)).1 hcoh1
        (insert r s.2 : Finset ℕ).finite_toSet hS
    refine ⟨(f', insert r s.2), ⟨hf'nice, ?_, ?_, ?_⟩, Finset.subset_insert _ _, hf'agree⟩
    · intro b hb
      rcases lt_or_eq_of_le hb with hb' | rfl
      · exact (hf'coh.mono hb'.le).trans ((hd (seq (n + 1)) (hseqlt _)).2 b hb')
      · exact hf'coh
    · rw [Finset.card_insert_of_notMem hr2, hcard]
    · intro x hx e he
      have := hf'avoid e he
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at this
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact this.1
      · intro hEq
        have hEq' : f' e = x := hEq
        exact this.2 (by rw [hEq']; exact hx)
  choose! next hnextQ hnextsub hnextagree using hstep
  set F : ℕ → St := fun n => Nat.rec ((fun _ => 0 : Ordinal.{0} → ℕ), (∅ : Finset ℕ))
    (fun n s => next n s) n with hFdef
  have hQF : ∀ n, Q n (F n) := by
    intro n
    induction n with
    | zero => exact hs0
    | succ n ih => exact hnextQ n (F n) ih
  have hsub1 : ∀ n, (F n).2 ⊆ (F (n + 1)).2 := fun n => hnextsub n (F n) (hQF n)
  have hagree1 : ∀ n, ∀ e < seq n, (F (n + 1)).1 e = (F n).1 e :=
    fun n => hnextagree n (F n) (hQF n)
  have hsub : ∀ m n, m ≤ n → (F m).2 ⊆ (F n).2 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n hmn ih => exact ih.trans (hsub1 n)
  have hagree : ∀ m n, m ≤ n → ∀ e < seq m, (F n).1 e = (F m).1 e := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro e _; rfl
    | succ n hmn ih =>
      intro e he
      have hlt : e < seq n := lt_of_lt_of_le he (hseqmono.monotone hmn)
      rw [hagree1 n e hlt, ih e he]
  -- the union of the stages
  set f : Ordinal.{0} → ℕ := fun e => if h : ∃ n, e < seq n then (F (Nat.find h)).1 e else 0
    with hfdef
  have hfval : ∀ n e, e < seq n → f e = (F n).1 e := by
    intro n e he
    have hex : ∃ m, e < seq m := ⟨n, he⟩
    rw [hfdef]
    simp only [dif_pos hex]
    have hm : e < seq (Nat.find hex) := Nat.find_spec hex
    have h1 : (F (max (Nat.find hex) n)).1 e = (F (Nat.find hex)).1 e :=
      hagree _ _ (le_max_left _ _) e hm
    have h2 : (F (max (Nat.find hex) n)).1 e = (F n).1 e :=
      hagree _ _ (le_max_right _ _) e he
    rw [← h1, h2]
  have hcof2 : ∀ e₁ < a, ∀ e₂ < a, ∃ n, e₁ < seq n ∧ e₂ < seq n := by
    intro e₁ h₁ e₂ h₂
    obtain ⟨n₁, hn₁⟩ := hseqcof e₁ h₁
    obtain ⟨n₂, hn₂⟩ := hseqcof e₂ h₂
    exact ⟨max n₁ n₂, lt_of_lt_of_le hn₁ (hseqmono.monotone (le_max_left _ _)),
      lt_of_lt_of_le hn₂ (hseqmono.monotone (le_max_right _ _))⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- injective below `a`
    intro e₁ h₁ e₂ h₂ hEq
    obtain ⟨n, hn₁, hn₂⟩ := hcof2 e₁ h₁ e₂ h₂
    refine (hQF n).1.1 e₁ hn₁ e₂ hn₂ ?_
    rw [← hfval n e₁ hn₁, ← hfval n e₂ hn₂]
    exact hEq
  · -- vanishes from `a` on
    intro e hae
    have : ¬ ∃ n, e < seq n := by
      rintro ⟨n, hn⟩
      exact absurd (lt_of_lt_of_le (hn.trans (hseqlt n)) hae) (lt_irrefl e)
    rw [hfdef]; simp only [dif_neg this]
  · -- omits infinitely many values
    have hWsub : ∀ n, ∀ x ∈ (F n).2, ∀ e < a, f e ≠ x := by
      intro n x hx e he
      obtain ⟨m, hm⟩ := hseqcof e he
      have hkm : e < seq (max m n) := lt_of_lt_of_le hm (hseqmono.monotone (le_max_left _ _))
      rw [hfval (max m n) e hkm]
      exact (hQF (max m n)).2.2.2 x (hsub n (max m n) (le_max_right _ _) hx) e hkm
    by_contra hfin
    rw [CoInf, Set.not_infinite] at hfin
    have hcard : ∀ n, n ≤ hfin.toFinset.card := by
      intro n
      rw [← (hQF n).2.2.1]
      apply Finset.card_le_card
      intro x hx
      rw [Set.Finite.mem_toFinset]
      exact fun e he => hWsub n x hx e he
    exact absurd (hcard (hfin.toFinset.card + 1)) (by omega)
  · -- coherent with all previous functions
    intro b hb
    obtain ⟨n, hn⟩ := hseqcof b hb
    refine Coh.trans (coh_of_eq ?_) ((hQF n).2.1 b hn.le)
    intro e he
    exact hfval n e (lt_trans he hn)

end Aronszajn

/-
The transfinite construction of a coherent sequence `E` of partial injections:
for every countable ordinal `a`, `E a` is injective below `a`, omits infinitely
many naturals, and agrees with `E b` below `b` up to finitely many exceptions,
for every `b < a`.
-/
import RequestProject.Aronszajn.Limit

open Ordinal Cardinal Set

namespace Aronszajn

/-- One step of the transfinite construction, all three cases at once. -/
