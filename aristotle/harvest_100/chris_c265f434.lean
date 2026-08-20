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

set_option grind.warning false

namespace Frontier

open Filter

section RamseyConstruction

/-- Pick an element of a set of naturals (junk value `0` if the set is empty). -/
noncomputable def pick (S : Set ℕ) : ℕ := if h : S.Nonempty then h.choose else 0

lemma pick_mem {S : Set ℕ} (h : S.Nonempty) : pick S ∈ S := by
  rw [pick, dif_pos h]; exact h.choose_spec

variable (c : ℕ → ℕ → Bool) (k : Bool) (A : Set ℕ)

/-- The decreasing sequence of sets from which the monochromatic set is chosen. -/
noncomputable def ramseySets : ℕ → Set ℕ
  | 0 => A
  | n + 1 => ramseySets n ∩ {m | c (pick (ramseySets n)) m = k ∧ pick (ramseySets n) < m}

/-- The monochromatic sequence. -/
noncomputable def ramseySeq (n : ℕ) : ℕ := pick (ramseySets c k A n)

lemma ramseySets_succ_subset (n : ℕ) : ramseySets c k A (n + 1) ⊆ ramseySets c k A n := by
  intro x hx
  exact hx.1

lemma ramseySets_antitone : Antitone (ramseySets c k A) :=
  antitone_nat_of_succ_le (fun n => ramseySets_succ_subset c k A n)

variable {c k A}

lemma ramseySets_mem (U : Ultrafilter ℕ) (hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U)
    (hA : A ∈ U) (hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U) :
    ∀ n, ramseySets c k A n ∈ U ∧ ramseySets c k A n ⊆ A := by
  intro n
  induction n with
  | zero => exact ⟨hA, subset_rfl⟩
  | succ n ih =>
    obtain ⟨hmem, hsub⟩ := ih
    have hne : (ramseySets c k A n).Nonempty := Ultrafilter.nonempty_of_mem hmem
    have hpick : pick (ramseySets c k A n) ∈ ramseySets c k A n := pick_mem hne
    have hcol : {m : ℕ | c (pick (ramseySets c k A n)) m = k} ∈ U := hAcol _ (hsub hpick)
    refine ⟨?_, (ramseySets_succ_subset c k A n).trans hsub⟩
    have : ramseySets c k A (n + 1)
        = ramseySets c k A n ∩ ({m : ℕ | c (pick (ramseySets c k A n)) m = k}
          ∩ {m : ℕ | pick (ramseySets c k A n) < m}) := by
      rw [ramseySets]
      ext x
      simp
    rw [this]
    exact Filter.inter_mem hmem (Filter.inter_mem hcol (hcof _))

lemma ramseySeq_mem (U : Ultrafilter ℕ) (hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U)
    (hA : A ∈ U) (hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U) (n : ℕ) :
    ramseySeq c k A n ∈ ramseySets c k A n :=
  pick_mem (Ultrafilter.nonempty_of_mem (ramseySets_mem U hcof hA hAcol n).1)

lemma ramseySeq_spec (U : Ultrafilter ℕ) (hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U)
    (hA : A ∈ U) (hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U) {i j : ℕ} (hij : i < j) :
    c (ramseySeq c k A i) (ramseySeq c k A j) = k ∧
      ramseySeq c k A i < ramseySeq c k A j := by
  have hmem : ramseySeq c k A j ∈ ramseySets c k A j :=
    ramseySeq_mem U hcof hA hAcol j
  have hsub : ramseySets c k A j ⊆ ramseySets c k A (i + 1) :=
    ramseySets_antitone c k A hij
  have := hsub hmem
  rw [ramseySets] at this
  exact this.2

end RamseyConstruction

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring `c`
of the (unordered) pairs of natural numbers by two colours there is an infinite set `S`
all of whose pairs receive the same colour `k`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (k : Bool), S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i < j → c i j = k := by
  classical
  let U : Ultrafilter ℕ := hyperfilter ℕ
  have hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U := by
    intro N
    have h : {m : ℕ | N < m} ∈ (Filter.cofinite : Filter ℕ) := by
      rw [Nat.cofinite_eq_atTop]
      exact Filter.eventually_gt_atTop N
    exact Filter.hyperfilter_le_cofinite h
  set f : ℕ → Bool := fun n => decide ({m : ℕ | c n m = true} ∈ U) with hfdef
  have hf : ∀ n, {m : ℕ | c n m = f n} ∈ U := by
    intro n
    by_cases h : {m : ℕ | c n m = true} ∈ U
    · simp [hfdef, h]
    · have hc : {m : ℕ | c n m = true}ᶜ ∈ U := (Ultrafilter.compl_mem_iff_notMem).2 h
      have : {m : ℕ | c n m = true}ᶜ = {m : ℕ | c n m = false} := by
        ext m; simp
      rw [this] at hc
      simpa [hfdef, h] using hc
  obtain ⟨k, hA⟩ : ∃ k : Bool, {n : ℕ | f n = k} ∈ U := by
    rcases Ultrafilter.mem_or_compl_mem U {n : ℕ | f n = true} with h | h
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      have : {n : ℕ | f n = true}ᶜ = {n : ℕ | f n = false} := by ext n; simp
      rwa [this] at h
  set A : Set ℕ := {n : ℕ | f n = k} with hAdef
  have hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U := by
    intro n hn
    have : f n = k := hn
    rw [← this]
    exact hf n
  set a : ℕ → ℕ := ramseySeq c k A with hadef
  have hmono : StrictMono a := fun i j hij =>
    (ramseySeq_spec U hcof hA hAcol hij).2
  refine ⟨Set.range a, k, Set.infinite_range_of_injective hmono.injective, ?_⟩
  rintro i ⟨p, rfl⟩ j ⟨q, rfl⟩ hlt
  have hpq : p < q := hmono.lt_iff_lt.mp hlt
  exact (ramseySeq_spec U hcof hA hAcol hpq).1

end Frontier

