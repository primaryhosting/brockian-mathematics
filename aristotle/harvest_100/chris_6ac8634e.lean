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

namespace Frontier

variable (c : ℕ → ℕ → Bool)

open Classical in
/-- The colour chosen at a stage of the Ramsey construction: `true` if the set of elements of
`S` above `sInf S` that are joined to `sInf S` in colour `true` is infinite, `false` otherwise. -/
noncomputable def ramseyColor (S : Set ℕ) : Bool :=
  if {x ∈ S | sInf S < x ∧ c (sInf S) x = true}.Infinite then true else false

/-- One step of the Ramsey construction: pass to the elements of `S` above `sInf S` joined to
`sInf S` by the colour `ramseyColor c S`. -/
noncomputable def ramseyNext (S : Set ℕ) : Set ℕ :=
  {x ∈ S | sInf S < x ∧ c (sInf S) x = ramseyColor c S}

/-- The nested sequence of infinite sets produced by the construction. -/
noncomputable def ramseySeq : ℕ → Set ℕ
  | 0 => Set.univ
  | n + 1 => ramseyNext c (ramseySeq n)

lemma ramseyNext_subset (S : Set ℕ) : ramseyNext c S ⊆ S := fun _ hx => hx.1

lemma sInf_lt_of_mem_ramseyNext {S : Set ℕ} {x : ℕ} (hx : x ∈ ramseyNext c S) :
    sInf S < x := hx.2.1

lemma color_of_mem_ramseyNext {S : Set ℕ} {x : ℕ} (hx : x ∈ ramseyNext c S) :
    c (sInf S) x = ramseyColor c S := hx.2.2

lemma infinite_gt_sInf {S : Set ℕ} (hS : S.Infinite) : {x ∈ S | sInf S < x}.Infinite := by
  have h : (S \ Set.Iic (sInf S)).Infinite := hS.diff (Set.finite_Iic _)
  refine h.mono ?_
  rintro x ⟨hxS, hx⟩
  exact ⟨hxS, by simpa using hx⟩

lemma ramseyNext_infinite {S : Set ℕ} (hS : S.Infinite) : (ramseyNext c S).Infinite := by
  classical
  by_cases h : {x ∈ S | sInf S < x ∧ c (sInf S) x = true}.Infinite
  · have hc : ramseyColor c S = true := by unfold ramseyColor; rw [if_pos h]
    simpa [ramseyNext, hc] using h
  · have hc : ramseyColor c S = false := by unfold ramseyColor; rw [if_neg h]
    have hbig := infinite_gt_sInf hS
    have hsub : {x ∈ S | sInf S < x} ⊆
        {x ∈ S | sInf S < x ∧ c (sInf S) x = true} ∪
          {x ∈ S | sInf S < x ∧ c (sInf S) x = false} := by
      rintro x ⟨hxS, hx⟩
      rcases Bool.eq_false_or_eq_true (c (sInf S) x) with hcx | hcx
      · exact Or.inl ⟨hxS, hx, hcx⟩
      · exact Or.inr ⟨hxS, hx, hcx⟩
    have hunion : ({x ∈ S | sInf S < x ∧ c (sInf S) x = true} ∪
        {x ∈ S | sInf S < x ∧ c (sInf S) x = false}).Infinite := hbig.mono hsub
    have hfalse : {x ∈ S | sInf S < x ∧ c (sInf S) x = false}.Infinite := by
      intro hfin
      exact hunion ((Set.not_infinite.mp h).union hfin)
    simpa [ramseyNext, hc] using hfalse

lemma ramseySeq_infinite : ∀ n : ℕ, (ramseySeq c n).Infinite
  | 0 => Set.infinite_univ
  | n + 1 => ramseyNext_infinite c (ramseySeq_infinite n)

lemma ramseySeq_antitone {n m : ℕ} (h : n ≤ m) : ramseySeq c m ⊆ ramseySeq c n := by
  induction m, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih => exact (ramseyNext_subset c _).trans ih

/-- The increasing sequence of "pivot" points of the construction. -/
noncomputable def ramseyPt (n : ℕ) : ℕ := sInf (ramseySeq c n)

lemma ramseyPt_mem (n : ℕ) : ramseyPt c n ∈ ramseySeq c n :=
  Nat.sInf_mem (ramseySeq_infinite c n).nonempty

lemma ramseyPt_strictMono : StrictMono (ramseyPt c) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact sInf_lt_of_mem_ramseyNext c (ramseyPt_mem c (n + 1))

lemma ramseyPt_color {n m : ℕ} (h : n < m) :
    c (ramseyPt c n) (ramseyPt c m) = ramseyColor c (ramseySeq c n) := by
  have hmem : ramseyPt c m ∈ ramseySeq c (n + 1) :=
    ramseySeq_antitone c h (ramseyPt_mem c m)
  exact color_of_mem_ramseyNext c hmem

/-- **Infinite Ramsey theorem for pairs and two colours**: for every 2-colouring `c` of the
(ordered) pairs of natural numbers there is an infinite set `S ⊆ ℕ` and a colour `i` such that
all pairs from `S` receive the colour `i`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (i : Bool), S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → c x y = i := by
  classical
  set e : ℕ → Bool := fun n => ramseyColor c (ramseySeq c n) with he
  have hpigeon : ∃ i : Bool, {n : ℕ | e n = i}.Infinite := by
    by_contra hcon
    push_neg at hcon
    have h1 := hcon true
    have h2 := hcon false
    have : (Set.univ : Set ℕ).Finite := by
      have : (Set.univ : Set ℕ) ⊆ {n : ℕ | e n = true} ∪ {n : ℕ | e n = false} := by
        intro n _
        rcases Bool.eq_false_or_eq_true (e n) with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact (h1.union h2).subset this
    exact Set.infinite_univ this
  obtain ⟨i, hi⟩ := hpigeon
  refine ⟨ramseyPt c '' {n : ℕ | e n = i}, i, hi.image ((ramseyPt_strictMono c).injective.injOn),
    ?_⟩
  rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩ hlt
  have hnm : n < m := (ramseyPt_strictMono c).lt_iff_lt.mp hlt
  rw [ramseyPt_color c hnm]
  exact hn

end Frontier

