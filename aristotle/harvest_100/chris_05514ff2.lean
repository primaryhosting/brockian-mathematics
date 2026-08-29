import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

open Classical in
/-- The `U`-generic colour at `n`: the colour `b` such that `{m | c n m = b} ∈ U`. -/
noncomputable def genColor (U : Ultrafilter ℕ) (c : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  if {m | c n m = true} ∈ U then true else false

lemma genColor_mem (U : Ultrafilter ℕ) (c : ℕ → ℕ → Bool) (n : ℕ) :
    {m | c n m = genColor U c n} ∈ U := by
  classical
  by_cases h : {m | c n m = true} ∈ U
  · simpa [genColor, h] using h
  · have hc : {m | c n m = true}ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.2 h
    have : {m | c n m = true}ᶜ = {m | c n m = false} := by
      ext m; simp [Bool.not_eq_true]
    rw [this] at hc
    simpa [genColor, h] using hc

open Classical in
/-- One step of the recursive construction: pick an element of the current set and shrink. -/
noncomputable def rstep (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) : ℕ × Set ℕ :=
  let m := if h : p.2.Nonempty then h.choose else 0
  (m, p.2 ∩ {x | c m x = b} ∩ Ioi m)

lemma rstep_snd_subset (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) :
    (rstep c b p).2 ⊆ p.2 := fun _ hx => hx.1.1

lemma rstep_fst_mem (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) (h : p.2.Nonempty) :
    (rstep c b p).1 ∈ p.2 := by
  classical
  simp only [rstep, dif_pos h]
  exact h.choose_spec

lemma rstep_snd_sub_color (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) :
    (rstep c b p).2 ⊆ {x | c (rstep c b p).1 x = b} ∩ Ioi (rstep c b p).1 :=
  fun _ hx => ⟨hx.1.2, hx.2⟩

/-- The iterates of `rstep` have decreasing second components. -/
lemma iterate_snd_antitone (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) :
    ∀ {k l : ℕ}, k ≤ l → ((rstep c b)^[l] p).2 ⊆ ((rstep c b)^[k] p).2 := by
  have key : ∀ k : ℕ, ((rstep c b)^[k + 1] p).2 ⊆ ((rstep c b)^[k] p).2 := by
    intro k
    rw [Function.iterate_succ_apply']
    exact rstep_snd_subset c b _
  intro k l hkl
  induction l with
  | zero => simpa using (Nat.le_zero.1 hkl) ▸ subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact (key n).trans (ih (Nat.lt_succ_iff.1 h))
    · have : k = n + 1 := le_antisymm hkl h
      subst this; exact subset_rfl

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring
`c : ℕ → ℕ → Bool` of the pairs of natural numbers there is an infinite set `S`
and a colour `b` such that every pair from `S` gets colour `b`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Bool) :
    ∃ S : Set ℕ, S.Infinite ∧ ∃ b : Bool, ∀ i ∈ S, ∀ j ∈ S, i < j → c i j = b := by
  classical
  set U : Ultrafilter ℕ := hyperfilter ℕ with hUdef
  have hUcof : (U : Filter ℕ) ≤ cofinite := Filter.hyperfilter_le_cofinite
  -- every member of `U` is infinite
  have hinf : ∀ s : Set ℕ, s ∈ U → s.Infinite := by
    intro s hs hfin
    exact (Ultrafilter.compl_notMem hs) (hUcof hfin.compl_mem_cofinite)
  -- tails belong to `U`
  have htail : ∀ m : ℕ, Ioi m ∈ U := by
    intro m
    refine hUcof ?_
    have : (Ioi m)ᶜ = Iic m := by ext x; simp
    simp [Filter.mem_cofinite, this, Set.finite_Iic]
  -- pigeonhole on the generic colours
  obtain ⟨b, hA⟩ : ∃ b : Bool, {n | genColor U c n = b} ∈ U := by
    by_cases h : {n | genColor U c n = true} ∈ U
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      have hc : {n | genColor U c n = true}ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.2 h
      have he : {n | genColor U c n = true}ᶜ = {n | genColor U c n = false} := by
        ext n; simp [Bool.not_eq_true]
      rwa [he] at hc
  set A : Set ℕ := {n | genColor U c n = b} with hAdef
  have hgood : ∀ n ∈ A, {m | c n m = b} ∈ U := by
    intro n hn
    have := genColor_mem U c n
    rwa [show genColor U c n = b from hn] at this
  set F : ℕ × Set ℕ → ℕ × Set ℕ := rstep c b with hF
  set p₀ : ℕ × Set ℕ := (0, A) with hp₀
  -- invariant
  have inv : ∀ k : ℕ, (F^[k] p₀).2 ∈ U ∧ (F^[k] p₀).2 ⊆ A := by
    intro k
    induction k with
    | zero => exact ⟨hA, subset_rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hmem, hsub⟩ := ih
      have hne : (F^[n] p₀).2.Nonempty := (hinf _ hmem).nonempty
      have hfst : (F (F^[n] p₀)).1 ∈ (F^[n] p₀).2 := rstep_fst_mem c b _ hne
      have hfstA : (F (F^[n] p₀)).1 ∈ A := hsub hfst
      constructor
      · show ((F^[n] p₀).2 ∩ {x | c _ x = b} ∩ Ioi _) ∈ U
        exact Filter.inter_mem (Filter.inter_mem hmem (hgood _ hfstA)) (htail _)
      · exact (rstep_snd_subset c b _).trans hsub
  -- the sequence
  set a : ℕ → ℕ := fun k => (F^[k + 1] p₀).1 with ha
  have hmem_prev : ∀ k : ℕ, a k ∈ (F^[k] p₀).2 := by
    intro k
    have hne : (F^[k] p₀).2.Nonempty := (hinf _ (inv k).1).nonempty
    have := rstep_fst_mem c b (F^[k] p₀) hne
    simpa [ha, Function.iterate_succ_apply'] using this
  have hshrink : ∀ k : ℕ, (F^[k + 1] p₀).2 ⊆ {x | c (a k) x = b} ∩ Ioi (a k) := by
    intro k
    have := rstep_snd_sub_color c b (F^[k] p₀)
    simpa [ha, Function.iterate_succ_apply'] using this
  have hkey : ∀ k l : ℕ, k < l → c (a k) (a l) = b ∧ a k < a l := by
    intro k l hkl
    have h1 : a l ∈ (F^[l] p₀).2 := hmem_prev l
    have h2 : (F^[l] p₀).2 ⊆ (F^[k + 1] p₀).2 :=
      iterate_snd_antitone c b p₀ (Nat.succ_le_of_lt hkl)
    exact hshrink k (h2 h1)
  have hmono : StrictMono a := strictMono_nat_of_lt_succ (fun n => (hkey n (n + 1) (Nat.lt_succ_self n)).2)
  refine ⟨Set.range a, Set.infinite_range_of_injective hmono.injective, b, ?_⟩
  rintro i ⟨k, rfl⟩ j ⟨l, rfl⟩ hij
  have hkl : k < l := by
    by_contra h
    exact absurd hij (not_lt.2 (hmono.monotone (not_lt.1 h)))
  exact (hkey k l hkl).1

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

