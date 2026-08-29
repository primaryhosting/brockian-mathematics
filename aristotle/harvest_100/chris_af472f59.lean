import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/
def RelativelyLarge (Y : Finset ℕ) : Prop :=
  ∃ y ∈ Y, (∀ z ∈ Y, y ≤ z) ∧ y ≤ Y.card

/-- `Y` is homogeneous of colour `i` for the colouring `c` of `n`-element sets. -/
def Homogeneous {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (Y : Finset ℕ) (i : Fin k) : Prop :=
  ∀ s ⊆ Y, s.card = n → c s = i

namespace PH

open Filter

/-- The ultrafilter limit of a function into a finite type, along the hyperfilter on `ℕ`. -/
noncomputable def ulim {k : ℕ} (f : ℕ → Fin k) : Fin k :=
  Classical.choose (Ultrafilter.eq_pure_of_finite (Ultrafilter.map f (hyperfilter ℕ)))

lemma ulim_spec {k : ℕ} (f : ℕ → Fin k) :
    ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), f x = ulim f := by
  have h := Classical.choose_spec
    (Ultrafilter.eq_pure_of_finite (Ultrafilter.map f (hyperfilter ℕ)))
  have h2 : {ulim f} ∈ Ultrafilter.map f (hyperfilter ℕ) := by
    rw [show Ultrafilter.map f (hyperfilter ℕ) = pure (ulim f) from h]
    simp
  rw [Ultrafilter.mem_map] at h2
  exact h2

/-- The auxiliary colourings: `G c r s` is the "limit colour" of the sets obtained from `s`
by adding `r` further (large) elements. -/
noncomputable def G {k : ℕ} (c : Finset ℕ → Fin k) : ℕ → Finset ℕ → Fin k
  | 0, s => c s
  | (r + 1), s => ulim (fun x => G c r (insert x s))

lemma G_succ_spec {k : ℕ} (c : Finset ℕ → Fin k) (r : ℕ) (s : Finset ℕ) :
    ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), G c r (insert x s) = G c (r + 1) s :=
  ulim_spec _

/-- The property required of the next element of the homogeneous chain. -/
def Good {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (F : Finset ℕ) (x : ℕ) : Prop :=
  0 < x ∧ (∀ y ∈ F, y < x) ∧
    ∀ s ∈ F.powerset, s.card < n → G c (n - s.card - 1) (insert x s) = G c (n - s.card) s

lemma exists_good {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (F : Finset ℕ) :
    ∃ x, Good n c F x := by
  have hle : (hyperfilter ℕ : Filter ℕ) ≤ atTop := Nat.hyperfilter_le_atTop
  have h1 : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), 0 < x := hle (eventually_gt_atTop 0)
  have h2 : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), ∀ y ∈ F, y < x := by
    rw [eventually_all_finset]
    intro y _
    exact hle (eventually_gt_atTop y)
  have h3 : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), ∀ s ∈ F.powerset, s.card < n →
      G c (n - s.card - 1) (insert x s) = G c (n - s.card) s := by
    rw [eventually_all_finset]
    intro s _
    by_cases hs : s.card < n
    · filter_upwards [G_succ_spec c (n - s.card - 1) s] with x hx _
      rw [hx]
      congr 1
      omega
    · filter_upwards with x hx
      exact absurd hx hs
  exact (h1.and (h2.and h3)).exists

/-- The next element of the homogeneous chain built after the finite set `F`. -/
noncomputable def next {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (F : Finset ℕ) : ℕ :=
  Classical.choose (exists_good n c F)

lemma next_spec {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (F : Finset ℕ) :
    Good n c F (next n c F) :=
  Classical.choose_spec (exists_good n c F)

/-- The increasing chain of finite sets whose union is homogeneous. -/
noncomputable def chain {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) : ℕ → Finset ℕ
  | 0 => ∅
  | (t + 1) => insert (next n c (chain n c t)) (chain n c t)

lemma chain_subset_succ {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    chain n c t ⊆ chain n c (t + 1) := by
  intro x hx
  simp [chain, Finset.mem_insert, hx]

lemma chain_mono {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) {t t' : ℕ} (h : t ≤ t') :
    chain n c t ⊆ chain n c t' := by
  have : Monotone (fun t => chain n c t) :=
    monotone_nat_of_le_succ (fun t => chain_subset_succ n c t)
  exact this h

lemma next_notMem {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (F : Finset ℕ) :
    next n c F ∉ F := by
  intro h
  exact absurd ((next_spec n c F).2.1 _ h) (lt_irrefl _)

lemma chain_card {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    (chain n c t).card = t := by
  induction t with
  | zero => simp [chain]
  | succ t ih =>
      rw [chain, Finset.card_insert_of_notMem (next_notMem n c _), ih]

lemma chain_pos {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    ∀ y ∈ chain n c t, 0 < y := by
  induction t with
  | zero => simp [chain]
  | succ t ih =>
      intro y hy
      rw [chain, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact (next_spec n c _).1
      · exact ih y hy

/-- The main homogeneity computation: every small subset of a stage of the chain gets the
"limit colour" of the empty set. -/
lemma chain_G {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    ∀ s ⊆ chain n c t, s.card ≤ n → G c (n - s.card) s = G c n ∅ := by
  induction t with
  | zero =>
      intro s hs _
      have : s = ∅ := by simpa [chain, Finset.subset_empty] using hs
      subst this
      simp
  | succ t ih =>
      intro s hs hcard
      set x : ℕ := next n c (chain n c t) with hxdef
      by_cases hxs : x ∈ s
      · have hs' : s.erase x ⊆ chain n c t := by
          intro y hy
          have hy1 : y ∈ s := Finset.mem_of_mem_erase hy
          have hy2 : y ≠ x := Finset.ne_of_mem_erase hy
          have := hs hy1
          rw [chain, Finset.mem_insert] at this
          rcases this with h | h
          · exact absurd h hy2
          · exact h
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨x, hxs⟩
        have hcard' : (s.erase x).card + 1 = s.card := by
          rw [Finset.card_erase_of_mem hxs]
          omega
        have hlt : (s.erase x).card < n := by omega
        have hins : insert x (s.erase x) = s := Finset.insert_erase hxs
        have hstep := (next_spec n c (chain n c t)).2.2 (s.erase x)
          (Finset.mem_powerset.mpr hs') hlt
        rw [hins] at hstep
        have hidx : n - (s.erase x).card - 1 = n - s.card := by omega
        rw [hidx] at hstep
        rw [hstep]
        exact ih (s.erase x) hs' (le_of_lt hlt)
      · have hs' : s ⊆ chain n c t := by
          intro y hy
          have := hs hy
          rw [chain, Finset.mem_insert] at this
          rcases this with h | h
          · exact absurd (show x ∈ s by rw [hxdef, ← h]; exact hy) hxs
          · exact h
        exact ih s hs' hcard

lemma chain_homogeneous {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    ∀ s ⊆ chain n c t, s.card = n → c s = G c n ∅ := by
  intro s hs hcard
  have := chain_G n c t s hs (le_of_eq hcard)
  rw [hcard] at this
  simpa [G] using this

end PH

open Filter PH

/-- **Infinite Ramsey theorem** (ultrafilter proof), packaged as an increasing chain of finite
homogeneous sets of positive integers with cardinalities `0, 1, 2, …`. -/
theorem exists_homogeneous_chain {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) :
    ∃ (B : ℕ → Finset ℕ) (i : Fin k),
      (∀ t t' : ℕ, t ≤ t' → B t ⊆ B t') ∧ (∀ t, (B t).card = t) ∧
        (∀ t, ∀ y ∈ B t, 0 < y) ∧ (∀ t, Homogeneous n c (B t) i) := by
  refine ⟨chain n c, G c n ∅, fun t t' h => chain_mono n c h, chain_card n c,
    chain_pos n c, fun t => ?_⟩
  intro s hs hcard
  exact chain_homogeneous n c t s hs hcard

/-- **Paris–Harrington strengthened finite Ramsey theorem.**

For all `n`, `k`, `m` there is `N` such that for every colouring `c` of the finite subsets of
`{1, …, N}` with `k` colours, there is a set `Y ⊆ {1, …, N}` with at least `m` elements which is
*relatively large* (its least element is at most its cardinality) and homogeneous for `c` on
`n`-element subsets.

This is the mathematical ("true") half of the Paris–Harrington theorem; the proof below is the
ultrafilter proof of the infinite Ramsey theorem combined with an ultrafilter compactness
argument.  The metamathematical half (unprovability in first-order Peano arithmetic) is a
statement about PA-derivability and is not formalised here. -/
theorem Paris_Harrington (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ Y : Finset ℕ,
      Y ⊆ Finset.Icc 1 N ∧ m ≤ Y.card ∧ RelativelyLarge Y ∧
        ∃ i : Fin k, Homogeneous n c Y i := by
  by_contra hcon
  -- For every `N` there is a colouring of `{1, …, N}` with no relatively large homogeneous set.
  have hall : ∀ N : ℕ, ∃ c : Finset ℕ → Fin k, ∀ Y : Finset ℕ, Y ⊆ Finset.Icc 1 N →
      m ≤ Y.card → RelativelyLarge Y → ∀ i : Fin k, ¬ Homogeneous n c Y i := by
    intro N
    by_contra h
    push_neg at h
    exact hcon ⟨N, h⟩
  choose C hC using hall
  -- The ultrafilter limit of these colourings.
  set cinf : Finset ℕ → Fin k := fun s => ulim (fun N => C N s)
  obtain ⟨B, i, hmono, hBcard, hBpos, hBhom⟩ := exists_homogeneous_chain n cinf
  obtain ⟨a, ha⟩ : ∃ a : ℕ, B 1 = {a} := Finset.card_eq_one.mp (hBcard 1)
  have haB1 : a ∈ B 1 := by rw [ha]; exact Finset.mem_singleton_self a
  have hapos : 0 < a := hBpos 1 a haB1
  set p : ℕ := max m a
  have hple : 1 ≤ p := le_trans hapos (le_max_right m a)
  have haY : a ∈ B p := hmono 1 p hple haB1
  have hYcard : (B p).card = p := hBcard p
  have hYne : (B p).Nonempty := ⟨a, haY⟩
  -- The relatively large homogeneous set for the limit colouring.
  have hrel : RelativelyLarge (B p) := by
    refine ⟨(B p).min' hYne, (B p).min'_mem hYne, fun z hz => (B p).min'_le z hz, ?_⟩
    calc (B p).min' hYne ≤ a := (B p).min'_le a haY
      _ ≤ p := le_max_right m a
      _ = (B p).card := hYcard.symm
  have hm : m ≤ (B p).card := by rw [hYcard]; exact le_max_left m a
  -- Find one `N` for which the colouring `C N` agrees with the limit colouring on `B p`.
  have hle : (hyperfilter ℕ : Filter ℕ) ≤ atTop := Nat.hyperfilter_le_atTop
  have h1 : ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), ∀ y ∈ B p, y ≤ N := by
    rw [eventually_all_finset]
    intro y _
    exact hle (eventually_ge_atTop y)
  have h2 : ∀ᶠ N in (hyperfilter ℕ : Filter ℕ), ∀ s ∈ (B p).powerset, C N s = cinf s := by
    rw [eventually_all_finset]
    intro s _
    exact ulim_spec (fun N => C N s)
  obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
  have hsub : B p ⊆ Finset.Icc 1 N := by
    intro y hy
    exact Finset.mem_Icc.mpr ⟨hBpos p y hy, hN1 y hy⟩
  have hhom : Homogeneous n (C N) (B p) i := by
    intro s hs hcards
    rw [hN2 s (Finset.mem_powerset.mpr hs)]
    exact hBhom p s hs hcards
  exact hC N (B p) hsub hm hrel i hhom

end Frontier

