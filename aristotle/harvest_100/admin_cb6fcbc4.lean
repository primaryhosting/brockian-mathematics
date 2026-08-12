import Mathlib
import RequestProject.Pentagonal.GenFun

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

/-!
# Euler's pentagonal number theorem

`Math.euler_pentagonal` states that the generating function of the partition numbers
`p(n) = Fintype.card n.Partition` is the inverse of the pentagonal series
`∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`, as formal power series over `ℤ`.

`Math.euler_pentagonal_prod` is the classical product form
`∏_{i ≥ 1} (1 - q^i) = ∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`.
-/

open scoped PowerSeries.WithPiTopology

namespace Math

/-- **Euler's pentagonal number theorem** for the partition generating function:
`(∑_{n ≥ 0} p(n) q^n) * (∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}) = 1` in `ℤ⟦X⟧`.
Here the inner sum over `k ∈ Finset.Icc (-n) n` picks out the (at most one) integer `k`
with `n = k(3k-1)/2`, contributing `(-1)^k`. -/
theorem euler_pentagonal :
    (PowerSeries.mk fun n => (Fintype.card n.Partition : ℤ)) *
      (PowerSeries.mk fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if k * (3 * k - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ k.natAbs else 0) = 1 :=
  Pentagonal.euler_pentagonal

/-- The product form of Euler's pentagonal number theorem:
`∏_{i ≥ 1} (1 - q^i) = ∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`. -/
theorem euler_pentagonal_prod :
    HasProd (fun i : ℕ => 1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
      (PowerSeries.mk fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        if k * (3 * k - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ k.natAbs else 0) :=
  Pentagonal.genFun_sgnChar_eq ▸ Pentagonal.hasProd_sgnChar

end Math

import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

We work with partitions of `n` into distinct positive parts, encoded as `Finset ℕ` not
containing `0` and with sum `n`.  The main result of this file is

`Pentagonal.sum_DPart : ∑ S ∈ DPart n, (-1) ^ S.card = pentCoeff n`

where `pentCoeff n` is `(-1)^k` if `n = k(3k-1)/2` for some `k : ℤ`, and `0` otherwise.
-/

open Finset

namespace Pentagonal

/-! ## Basic quantities attached to a finite set of positive integers -/

/-- The smallest element of `S` (junk value `0` if `S` is empty). -/
def mn (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.min' h else 0

/-- The largest element of `S` (junk value `0` if `S` is empty). -/
def mx (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.max' h else 0

/-- The length of the "staircase" at the top of `S`: the largest `t` such that
`mx S - t + 1, …, mx S` all belong to `S`. -/
def runLen (S : Finset ℕ) : ℕ :=
  Nat.findGreatest (fun t => Finset.Icc (mx S + 1 - t) (mx S) ⊆ S) (mx S)

/-- Shift up by one all numbers `≥ a`. -/
def up (a x : ℕ) : ℕ := if a ≤ x then x + 1 else x

/-- Shift down by one all numbers `≥ a`. -/
def dn (a x : ℕ) : ℕ := if a ≤ x then x - 1 else x

/-- Franklin's involution. -/
def franklin (S : Finset ℕ) : Finset ℕ :=
  if mn S ≤ runLen S then (S.erase (mn S)).image (up (mx S + 1 - mn S))
  else insert (runLen S) (S.image (dn (mx S + 1 - runLen S)))

/-- The sets on which Franklin's involution is not defined. -/
def Exceptional (S : Finset ℕ) : Prop :=
  (mn S ≤ runLen S ∧ mx S < 2 * mn S) ∨ (runLen S < mn S ∧ mx S = 2 * runLen S)

instance : DecidablePred Exceptional := fun S => by unfold Exceptional; infer_instance

/-- Partitions of `n` into distinct positive parts, encoded as finite sets. -/
def DPart (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (n + 1)).powerset.filter (fun S => 0 ∉ S ∧ ∑ i ∈ S, i = n)

/-- The finite set attached to `k : ℤ`: `{k, …, 2k-1}` for `k > 0`, and
`{|k|+1, …, 2|k|}` for `k ≤ 0`.  Its sum is `k(3k-1)/2` and its cardinality is `|k|`. -/
def pentSet (k : ℤ) : Finset ℕ :=
  if 0 < k then Finset.Icc k.toNat (2 * k.toNat - 1) else Finset.Icc (k.natAbs + 1) (2 * k.natAbs)

/-- The coefficients of `∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`. -/
def pentCoeff (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if k * (3 * k - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ k.natAbs
    else 0

/-! ## Elementary lemmas -/

theorem mem_DPart {n : ℕ} {S : Finset ℕ} : S ∈ DPart n ↔ 0 ∉ S ∧ ∑ i ∈ S, i = n := by
  simp only [DPart, mem_filter, mem_powerset]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, h0, hsum⟩
    have : x ≤ ∑ i ∈ S, i := Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp only [mem_range]
    omega

theorem mn_mem {S : Finset ℕ} (h : S.Nonempty) : mn S ∈ S := by
  rw [mn, dif_pos h]; exact S.min'_mem h

theorem mn_le {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : mn S ≤ x := by
  have h : S.Nonempty := ⟨x, hx⟩
  rw [mn, dif_pos h]; exact S.min'_le x hx

theorem mx_mem {S : Finset ℕ} (h : S.Nonempty) : mx S ∈ S := by
  rw [mx, dif_pos h]; exact S.max'_mem h

theorem le_mx {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : x ≤ mx S := by
  have h : S.Nonempty := ⟨x, hx⟩
  rw [mx, dif_pos h]; exact S.le_max' x hx

theorem mn_eq {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) (h : ∀ x ∈ S, a ≤ x) : mn S = a :=
  le_antisymm (mn_le ha) (h _ (mn_mem ⟨a, ha⟩))

theorem mx_eq {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) (h : ∀ x ∈ S, x ≤ a) : mx S = a :=
  le_antisymm (h _ (mx_mem ⟨a, ha⟩)) (le_mx ha)

theorem runLen_subset {S : Finset ℕ} : Finset.Icc (mx S + 1 - runLen S) (mx S) ⊆ S :=
  Nat.findGreatest_spec (P := fun t => Finset.Icc (mx S + 1 - t) (mx S) ⊆ S) (m := 0)
    (n := mx S) (Nat.zero_le _) (by
      simp only [Nat.sub_zero]
      rw [Finset.Icc_eq_empty (by omega)]
      exact Finset.empty_subset _)

theorem runLen_le_mx (S : Finset ℕ) : runLen S ≤ mx S := Nat.findGreatest_le _

theorem one_le_mx {S : Finset ℕ} (h : S.Nonempty) (h0 : 0 ∉ S) : 1 ≤ mx S := by
  have := mx_mem h
  rcases Nat.eq_zero_or_pos (mx S) with h1 | h1
  · exact absurd (h1 ▸ this) h0
  · exact h1

theorem one_le_runLen {S : Finset ℕ} (h : S.Nonempty) (h0 : 0 ∉ S) : 1 ≤ runLen S := by
  refine Nat.le_findGreatest (one_le_mx h h0) ?_
  intro x hx
  simp only [mem_Icc, Nat.add_sub_cancel] at hx
  have : x = mx S := le_antisymm hx.2 hx.1
  exact this ▸ mx_mem h

theorem notMem_mx_sub_runLen {S : Finset ℕ} (h0 : 0 ∉ S) :
    mx S - runLen S ∉ S := by
  rcases eq_or_lt_of_le (runLen_le_mx S) with heq | hlt
  · rw [heq, Nat.sub_self]; exact h0
  · intro hmem
    have key : ¬ (Finset.Icc (mx S + 1 - (runLen S + 1)) (mx S) ⊆ S) :=
      Nat.findGreatest_is_greatest (P := fun t => Finset.Icc (mx S + 1 - t) (mx S) ⊆ S)
        (k := runLen S + 1) (n := mx S) (Nat.lt_succ_self _) (by omega)
    refine key fun x hx => ?_
    simp only [mem_Icc] at hx
    rcases eq_or_lt_of_le hx.1 with heq | hlt'
    · have : x = mx S - runLen S := by omega
      exact this ▸ hmem
    · exact runLen_subset (mem_Icc.mpr ⟨by omega, hx.2⟩)

/-- Characterisation of the run length. -/
theorem runLen_eq {S : Finset ℕ} {t : ℕ} (ht : t ≤ mx S)
    (h1 : Finset.Icc (mx S + 1 - t) (mx S) ⊆ S) (h2 : mx S - t ∉ S) : runLen S = t := by
  refine le_antisymm ?_ (Nat.le_findGreatest ht h1)
  by_contra hcon
  push_neg at hcon
  exact h2 (runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩))

/-- The elements of `S` that are at least `mx S + 1 - t` are exactly the top run,
provided `t ≤ runLen S`. -/
theorem filter_ge_eq_Icc {S : Finset ℕ} {t : ℕ} (ht : t ≤ runLen S) :
    S.filter (fun x => mx S + 1 - t ≤ x) = Finset.Icc (mx S + 1 - t) (mx S) := by
  ext x
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨hx, h⟩; exact ⟨h, le_mx hx⟩
  · rintro ⟨h1, h2⟩
    exact ⟨runLen_subset (mem_Icc.mpr ⟨by omega, h2⟩), h1⟩

/-! ## The two shifting operations -/

theorem up_injective (a : ℕ) : Function.Injective (up a) := by
  intro x y h
  simp only [up] at h
  split_ifs at h <;> omega

theorem sum_image_up (S : Finset ℕ) (a : ℕ) :
    ∑ x ∈ S.image (up a), x = (∑ x ∈ S, x) + (S.filter (fun x => a ≤ x)).card := by
  rw [Finset.sum_image (fun x _ y _ h => up_injective a h), Finset.card_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [up]
  split_ifs <;> omega

theorem card_image_up (S : Finset ℕ) (a : ℕ) : (S.image (up a)).card = S.card :=
  Finset.card_image_of_injective S (up_injective a)

theorem dn_injOn {S : Finset ℕ} {a : ℕ} (h : a - 1 ∉ S) : Set.InjOn (dn a) S := by
  intro x hx y hy hxy
  have hx' : x ≠ a - 1 := fun e => h (e ▸ hx)
  have hy' : y ≠ a - 1 := fun e => h (e ▸ hy)
  simp only [dn] at hxy
  split_ifs at hxy <;> omega

theorem sum_image_dn {S : Finset ℕ} {a : ℕ} (h : a - 1 ∉ S) :
    (∑ x ∈ S.image (dn a), x) + (S.filter (fun x => a ≤ x)).card = ∑ x ∈ S, x := by
  rw [Finset.sum_image (fun x hx y hy hxy => dn_injOn h hx hy hxy), Finset.card_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x ≠ a - 1 := fun e => h (e ▸ hx)
  simp only [dn]
  split_ifs <;> omega

theorem card_image_dn {S : Finset ℕ} {a : ℕ} (h : a - 1 ∉ S) :
    (S.image (dn a)).card = S.card :=
  Finset.card_image_of_injOn (dn_injOn h)

/-! ## Basic facts about elements of `DPart n` -/

theorem DPart_facts {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n) :
    0 ∉ S ∧ (∑ i ∈ S, i) = n ∧ S.Nonempty ∧ 1 ≤ mn S ∧ mn S ≤ mx S ∧ 1 ≤ runLen S ∧
      runLen S ≤ mx S := by
  obtain ⟨h0, hsum⟩ := mem_DPart.mp hS
  have hne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | h
    · simp only [Finset.sum_empty] at hsum; omega
    · exact h
  have hm1 : 1 ≤ mn S := Nat.pos_of_ne_zero fun h => h0 (h ▸ mn_mem hne)
  exact ⟨h0, hsum, hne, hm1, le_mx (mn_mem hne), one_le_runLen hne h0, runLen_le_mx S⟩

/-! ## Case A : the smallest part is at most the run length -/

section CaseA

variable {n : ℕ} {S : Finset ℕ}

theorem mem_franklin_caseA (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) (x : ℕ) :
    x ∈ franklin S ↔ ((x ∈ S ∧ x ≠ mn S ∧ x ≤ mx S - mn S) ∨
      (mx S + 2 - mn S ≤ x ∧ x ≤ mx S + 1)) := by
  have hm1 : 1 ≤ mn S := Nat.pos_of_ne_zero fun h => h0 (h ▸ mn_mem hne)
  have hsub : Finset.Icc (mx S + 1 - mn S) (mx S) ⊆ S := by
    intro y hy
    simp only [mem_Icc] at hy
    exact runLen_subset (mem_Icc.mpr ⟨by omega, hy.2⟩)
  rw [franklin, if_pos hA]
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    have hyM : y ≤ mx S := le_mx hy2
    by_cases hy : mx S + 1 - mn S ≤ y
    · right
      simp only [up, if_pos hy]
      omega
    · left
      simp only [up, if_neg hy]
      exact ⟨hy2, hy1, by omega⟩
  · rintro (⟨hx1, hx2, hx3⟩ | ⟨hx1, hx2⟩)
    · refine ⟨x, ⟨hx2, hx1⟩, ?_⟩
      simp only [up, if_neg (by omega : ¬ (mx S + 1 - mn S ≤ x))]
    · refine ⟨x - 1, ⟨by omega, hsub (mem_Icc.mpr ⟨by omega, by omega⟩)⟩, ?_⟩
      simp only [up, if_pos (by omega : mx S + 1 - mn S ≤ x - 1)]
      omega

theorem franklin_caseA_filter (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) :
    ((S.erase (mn S)).filter (fun x => mx S + 1 - mn S ≤ x)).card = mn S := by
  have hm1 : 1 ≤ mn S := Nat.pos_of_ne_zero fun h => h0 (h ▸ mn_mem hne)
  have hmM : mn S ≤ mx S := le_mx (mn_mem hne)
  have : (S.erase (mn S)).filter (fun x => mx S + 1 - mn S ≤ x) =
      S.filter (fun x => mx S + 1 - mn S ≤ x) := by
    ext y
    simp only [mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hy⟩, h⟩; exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩; exact ⟨⟨by omega, hy⟩, h⟩
  rw [this, filter_ge_eq_Icc hA, Nat.card_Icc]
  omega

theorem franklin_caseA_mem (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : franklin S ∈ DPart n := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  rw [mem_DPart]
  constructor
  · intro hmem
    rcases (mem_franklin_caseA h0 hne hA hM 0).mp hmem with ⟨h, -, -⟩ | ⟨h, -⟩
    · exact h0 h
    · omega
  · rw [franklin, if_pos hA, sum_image_up, franklin_caseA_filter h0 hne hA hM]
    have h : mn S + ∑ x ∈ S.erase (mn S), x = ∑ x ∈ S, x :=
      Finset.add_sum_erase S (fun i => i) (mn_mem hne)
    omega

theorem franklin_caseA_card (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S) :
    (franklin S).card + 1 = S.card := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  rw [franklin, if_pos hA, card_image_up, Finset.card_erase_of_mem (mn_mem hne)]
  have : 1 ≤ S.card := Finset.card_pos.mpr hne
  omega

theorem franklin_caseA_mx (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : mx (franklin S) = mx S + 1 := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  refine mx_eq ((mem_franklin_caseA h0 hne hA hM _).mpr (Or.inr ⟨by omega, le_rfl⟩)) ?_
  intro x hx
  rcases (mem_franklin_caseA h0 hne hA hM x).mp hx with ⟨hx1, -, -⟩ | ⟨-, hx2⟩
  · have := le_mx hx1; omega
  · exact hx2

theorem franklin_caseA_runLen (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : runLen (franklin S) = mn S := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hmxT := franklin_caseA_mx hS hn hA hM
  refine runLen_eq (by omega) ?_ ?_
  · intro x hx
    simp only [mem_Icc, hmxT] at hx
    exact (mem_franklin_caseA h0 hne hA hM x).mpr (Or.inr ⟨by omega, by omega⟩)
  · intro hmem
    rw [hmxT] at hmem
    rcases (mem_franklin_caseA h0 hne hA hM _).mp hmem with ⟨-, -, h⟩ | ⟨h, -⟩ <;> omega

theorem franklin_caseA_mn_gt (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : runLen (franklin S) < mn (franklin S) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hTne : (franklin S).Nonempty :=
    ⟨mx S + 1, (mem_franklin_caseA h0 hne hA hM _).mpr (Or.inr ⟨by omega, le_rfl⟩)⟩
  rw [franklin_caseA_runLen hS hn hA hM]
  rcases (mem_franklin_caseA h0 hne hA hM _).mp (mn_mem hTne) with ⟨hx1, hx2, -⟩ | ⟨h, -⟩
  · have := mn_le hx1; omega
  · omega

theorem franklin_caseA_notExceptional (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : ¬ Exceptional (franklin S) := by
  have h1 := franklin_caseA_mn_gt hS hn hA hM
  have h2 := franklin_caseA_runLen hS hn hA hM
  have h3 := franklin_caseA_mx hS hn hA hM
  rintro (⟨h, -⟩ | ⟨-, h⟩)
  · omega
  · omega

theorem franklin_caseA_involutive (hS : S ∈ DPart n) (hn : 1 ≤ n) (hA : mn S ≤ runLen S)
    (hM : 2 * mn S ≤ mx S) : franklin (franklin S) = S := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hmxT := franklin_caseA_mx hS hn hA hM
  have hrT := franklin_caseA_runLen hS hn hA hM
  have hgt := franklin_caseA_mn_gt hS hn hA hM
  have hsub : Finset.Icc (mx S + 1 - mn S) (mx S) ⊆ S := by
    intro y hy
    simp only [mem_Icc] at hy
    exact runLen_subset (mem_Icc.mpr ⟨by omega, hy.2⟩)
  rw [franklin, if_neg (by omega), hrT, hmxT]
  ext x
  simp only [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact mn_mem hne
    · rcases (mem_franklin_caseA h0 hne hA hM y).mp hy with ⟨hy1, -, hy3⟩ | ⟨hy1, hy2⟩
      · rwa [dn, if_neg (by omega)]
      · rw [dn, if_pos (by omega)]
        exact hsub (mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro hx
    by_cases hxm : x = mn S
    · exact Or.inl hxm
    have hxmx : x ≤ mx S := le_mx hx
    have hxmn : mn S ≤ x := mn_le hx
    by_cases hlow : x ≤ mx S - mn S
    · refine Or.inr ⟨x, (mem_franklin_caseA h0 hne hA hM x).mpr (Or.inl ⟨hx, hxm, hlow⟩), ?_⟩
      rw [dn, if_neg (by omega)]
    · refine Or.inr ⟨x + 1, (mem_franklin_caseA h0 hne hA hM (x + 1)).mpr
        (Or.inr ⟨by omega, by omega⟩), ?_⟩
      rw [dn, if_pos (by omega)]
      omega

end CaseA

/-! ## Case B : the smallest part exceeds the run length -/

section CaseB

variable {n : ℕ} {S : Finset ℕ}

theorem caseB_two_mul_lt (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : 2 * runLen S < mx S := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hmem : mx S + 1 - runLen S ∈ S :=
    runLen_subset (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have := mn_le hmem
  omega

theorem mem_franklin_caseB (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) (x : ℕ) :
    x ∈ franklin S ↔ (x = runLen S ∨ (x ∈ S ∧ x + runLen S < mx S) ∨
      (mx S - runLen S ≤ x ∧ x ≤ mx S - 1)) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  rw [franklin, if_neg (not_le.mpr hB)]
  simp only [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact Or.inl rfl
    · have hyM := le_mx hy
      have hym := mn_le hy
      have hyne : y ≠ mx S - runLen S := fun e => hnot (e ▸ hy)
      by_cases hc : mx S + 1 - runLen S ≤ y
      · refine Or.inr (Or.inr ?_)
        rw [dn, if_pos hc]
        omega
      · refine Or.inr (Or.inl ?_)
        rw [dn, if_neg hc]
        exact ⟨hy, by omega⟩
  · rintro (rfl | ⟨hx, hx2⟩ | ⟨hx1, hx2⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hx, by rw [dn, if_neg (by omega)]⟩
    · refine Or.inr ⟨x + 1, runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩), ?_⟩
      rw [dn, if_pos (by omega)]
      omega

theorem franklin_caseB_notMem (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) :
    runLen S ∉ S.image (dn (mx S + 1 - runLen S)) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  intro hmem
  have : runLen S ∈ franklin S := by
    rw [franklin, if_neg (not_le.mpr hB)]
    exact Finset.mem_insert_of_mem hmem
  simp only [Finset.mem_image] at hmem
  obtain ⟨y, hy, hxy⟩ := hmem
  have hym := mn_le hy
  have hyM := le_mx hy
  rw [dn] at hxy
  split_ifs at hxy <;> omega

theorem franklin_caseB_mem (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : franklin S ∈ DPart n := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  rw [mem_DPart]
  constructor
  · intro hmem
    rcases (mem_franklin_caseB hS hn hB hM 0).mp hmem with h | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · exact h0 h
    · omega
  · rw [franklin, if_neg (not_le.mpr hB),
      Finset.sum_insert (franklin_caseB_notMem hS hn hB hM)]
    have hnot' : mx S + 1 - runLen S - 1 ∉ S := by
      have he : mx S + 1 - runLen S - 1 = mx S - runLen S := by omega
      rw [he]; exact hnot
    have hd : (∑ x ∈ S.image (dn (mx S + 1 - runLen S)), x) +
        (S.filter (fun x => mx S + 1 - runLen S ≤ x)).card = ∑ x ∈ S, x :=
      sum_image_dn hnot'
    rw [filter_ge_eq_Icc (le_refl (runLen S)), Nat.card_Icc] at hd
    omega

theorem franklin_caseB_card (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : (franklin S).card = S.card + 1 := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  have hnot' : mx S + 1 - runLen S - 1 ∉ S := by
    have he : mx S + 1 - runLen S - 1 = mx S - runLen S := by omega
    rw [he]; exact hnot
  rw [franklin, if_neg (not_le.mpr hB),
    Finset.card_insert_of_notMem (franklin_caseB_notMem hS hn hB hM),
    card_image_dn hnot']

theorem franklin_caseB_mx (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : mx (franklin S) = mx S - 1 := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  refine mx_eq ((mem_franklin_caseB hS hn hB hM _).mpr (Or.inr (Or.inr ⟨by omega, le_rfl⟩))) ?_
  intro x hx
  rcases (mem_franklin_caseB hS hn hB hM x).mp hx with rfl | ⟨hx1, hx2⟩ | ⟨-, hx2⟩
  · omega
  · omega
  · exact hx2

theorem franklin_caseB_mn (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : mn (franklin S) = runLen S := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  refine mn_eq ((mem_franklin_caseB hS hn hB hM _).mpr (Or.inl rfl)) ?_
  intro x hx
  rcases (mem_franklin_caseB hS hn hB hM x).mp hx with rfl | ⟨hx1, -⟩ | ⟨hx1, -⟩
  · exact le_rfl
  · have := mn_le hx1; omega
  · omega

theorem franklin_caseB_le_runLen (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : mn (franklin S) ≤ runLen (franklin S) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hmxT := franklin_caseB_mx hS hn hB hM
  rw [franklin_caseB_mn hS hn hB hM]
  refine Nat.le_findGreatest (by omega) ?_
  intro x hx
  simp only [mem_Icc, hmxT] at hx
  exact (mem_franklin_caseB hS hn hB hM x).mpr (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem franklin_caseB_notExceptional (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : ¬ Exceptional (franklin S) := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hmxT := franklin_caseB_mx hS hn hB hM
  have hmnT := franklin_caseB_mn hS hn hB hM
  have hle := franklin_caseB_le_runLen hS hn hB hM
  rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega

theorem franklin_caseB_involutive (hS : S ∈ DPart n) (hn : 1 ≤ n) (hB : runLen S < mn S)
    (hM : mx S ≠ 2 * runLen S) : franklin (franklin S) = S := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have h2r := caseB_two_mul_lt hS hn hB hM
  have hmxT := franklin_caseB_mx hS hn hB hM
  have hmnT := franklin_caseB_mn hS hn hB hM
  have hle := franklin_caseB_le_runLen hS hn hB hM
  have hnot : mx S - runLen S ∉ S := notMem_mx_sub_runLen h0
  rw [franklin, if_pos hle, hmnT, hmxT]
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    rcases (mem_franklin_caseB hS hn hB hM y).mp hy2 with rfl | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
    · exact absurd rfl hy1
    · rwa [up, if_neg (by omega)]
    · rw [up, if_pos (by omega)]
      exact runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro hx
    have hxm := mn_le hx
    have hxM := le_mx hx
    have hxne : x ≠ mx S - runLen S := fun e => hnot (e ▸ hx)
    by_cases hlow : x + runLen S < mx S
    · refine ⟨x, ⟨by omega, (mem_franklin_caseB hS hn hB hM x).mpr (Or.inr (Or.inl ⟨hx, hlow⟩))⟩,
        ?_⟩
      rw [up, if_neg (by omega)]
    · refine ⟨x - 1, ⟨by omega, (mem_franklin_caseB hS hn hB hM (x - 1)).mpr
        (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩, ?_⟩
      rw [up, if_pos (by omega)]
      omega

end CaseB

/-! ## The involution -/

/-- On a non-exceptional set, exactly one of the two cases of Franklin's map applies. -/
theorem franklin_cases {S : Finset ℕ} (hexc : ¬ Exceptional S) :
    (mn S ≤ runLen S ∧ 2 * mn S ≤ mx S) ∨ (runLen S < mn S ∧ mx S ≠ 2 * runLen S) := by
  rw [Exceptional] at hexc
  push_neg at hexc
  by_cases h : mn S ≤ runLen S
  · exact Or.inl ⟨h, hexc.1 h⟩
  · exact Or.inr ⟨by omega, hexc.2 (by omega)⟩

theorem franklin_mem {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : ¬ Exceptional S) : franklin S ∈ DPart n := by
  rcases franklin_cases hexc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact franklin_caseA_mem hS hn h1 h2
  · exact franklin_caseB_mem hS hn h1 h2

theorem franklin_notExceptional {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : ¬ Exceptional S) : ¬ Exceptional (franklin S) := by
  rcases franklin_cases hexc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact franklin_caseA_notExceptional hS hn h1 h2
  · exact franklin_caseB_notExceptional hS hn h1 h2

theorem franklin_involutive {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : ¬ Exceptional S) : franklin (franklin S) = S := by
  rcases franklin_cases hexc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact franklin_caseA_involutive hS hn h1 h2
  · exact franklin_caseB_involutive hS hn h1 h2

theorem franklin_card_ne {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : ¬ Exceptional S) : (franklin S).card ≠ S.card := by
  rcases franklin_cases hexc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := franklin_caseA_card hS hn h1; omega
  · have := franklin_caseB_card hS hn h1 h2; omega

theorem franklin_sign {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : ¬ Exceptional S) :
    (-1 : ℤ) ^ S.card + (-1 : ℤ) ^ (franklin S).card = 0 := by
  have key : ∀ c : ℕ, (-1 : ℤ) ^ (c + 1) + (-1 : ℤ) ^ c = 0 := by
    intro c; rw [pow_succ]; ring
  rcases franklin_cases hexc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hc := franklin_caseA_card hS hn h1
    rw [← hc]
    exact key _
  · have hc := franklin_caseB_card hS hn h1 h2
    rw [hc, add_comm]
    exact key _

theorem sum_nonExceptional (n : ℕ) (hn : 1 ≤ n) :
    ∑ S ∈ (DPart n).filter (fun S => ¬ Exceptional S), (-1 : ℤ) ^ S.card = 0 := by
  refine Finset.sum_involution (fun S _ => franklin S) ?_ ?_ ?_ ?_
  · intro S hSmem
    rw [Finset.mem_filter] at hSmem
    exact franklin_sign hSmem.1 hn hSmem.2
  · intro S hSmem _
    rw [Finset.mem_filter] at hSmem
    intro hcon
    exact franklin_card_ne hSmem.1 hn hSmem.2 (congrArg Finset.card hcon)
  · intro S hSmem
    rw [Finset.mem_filter] at hSmem ⊢
    exact ⟨franklin_mem hSmem.1 hn hSmem.2, franklin_notExceptional hSmem.1 hn hSmem.2⟩
  · intro S hSmem
    rw [Finset.mem_filter] at hSmem
    exact franklin_involutive hSmem.1 hn hSmem.2

/-! ## The exceptional sets -/

theorem sum_Icc_mul_two (a b : ℕ) (h : a ≤ b + 1) :
    (∑ i ∈ Finset.Icc a b, i) * 2 + a * (a - 1) = (b + 1) * b := by
  have h1 : Finset.Icc a b = Finset.Ico a (b + 1) := (Finset.Ico_add_one_right_eq_Icc a b).symm
  have h2 : ∑ i ∈ Finset.Ico 0 a, i + ∑ i ∈ Finset.Ico a (b + 1), i =
      ∑ i ∈ Finset.Ico 0 (b + 1), i := Finset.sum_Ico_consecutive _ (Nat.zero_le a) h
  rw [← Finset.range_eq_Ico] at h2
  have h3 := Finset.sum_range_id_mul_two a
  have h4 := Finset.sum_range_id_mul_two (b + 1)
  simp only [Nat.add_sub_cancel] at h4
  rw [h1]
  have h5 : (∑ i ∈ Finset.range a, i + ∑ i ∈ Finset.Ico a (b + 1), i) * 2 =
      (∑ i ∈ Finset.range (b + 1), i) * 2 := by rw [h2]
  rw [add_mul, h3, h4] at h5
  linarith

theorem sum_pentSet_mul_two (k : ℤ) :
    ((∑ i ∈ pentSet k, i : ℕ) : ℤ) * 2 = k * (3 * k - 1) := by
  rcases lt_or_ge 0 k with hk | hk
  · obtain ⟨c, hc⟩ : ∃ c, k.toNat = c + 1 := ⟨k.toNat - 1, by omega⟩
    have hk' : k = (c : ℤ) + 1 := by omega
    have he : 2 * k.toNat - 1 = 2 * c + 1 := by omega
    rw [pentSet, if_pos hk, he, hc]
    have h := sum_Icc_mul_two (c + 1) (2 * c + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have hcast : ((∑ i ∈ Finset.Icc (c + 1) (2 * c + 1), i : ℕ) : ℤ) * 2 + ((c : ℤ) + 1) * c =
        (2 * (c : ℤ) + 1 + 1) * (2 * c + 1) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
    rw [hk']
    linear_combination hcast
  · have hk0 : (k.natAbs : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hk
    rw [pentSet, if_neg (by omega)]
    have h := sum_Icc_mul_two (k.natAbs + 1) (2 * k.natAbs) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have hcast : ((∑ i ∈ Finset.Icc (k.natAbs + 1) (2 * k.natAbs), i : ℕ) : ℤ) * 2 +
        ((k.natAbs : ℤ) + 1) * (k.natAbs : ℤ) =
        (2 * (k.natAbs : ℤ) + 1) * (2 * (k.natAbs : ℤ)) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
    rw [hk0] at hcast
    linear_combination hcast

theorem pentSet_card (k : ℤ) : (pentSet k).card = k.natAbs := by
  rcases lt_or_ge 0 k with hk | hk
  · rw [pentSet, if_pos hk, Nat.card_Icc]
    omega
  · rw [pentSet, if_neg (by omega), Nat.card_Icc]
    omega

/-- The basic invariants of an interval `[a, b]`. -/
theorem Icc_facts {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    mn (Finset.Icc a b) = a ∧ mx (Finset.Icc a b) = b ∧
      runLen (Finset.Icc a b) = b + 1 - a := by
  have hmn : mn (Finset.Icc a b) = a := by
    refine mn_eq (mem_Icc.mpr ⟨le_rfl, hab⟩) fun x hx => (mem_Icc.mp hx).1
  have hmx : mx (Finset.Icc a b) = b := by
    refine mx_eq (mem_Icc.mpr ⟨hab, le_rfl⟩) fun x hx => (mem_Icc.mp hx).2
  refine ⟨hmn, hmx, runLen_eq (by omega) ?_ ?_⟩
  · intro x hx
    rw [hmx] at hx
    simp only [mem_Icc] at hx ⊢
    omega
  · rw [hmx]
    simp only [mem_Icc]
    omega

theorem pentSet_exceptional {k : ℤ} (hk : k ≠ 0) : Exceptional (pentSet k) := by
  rcases lt_or_ge 0 k with hpos | hneg
  · obtain ⟨c, hc⟩ : ∃ c, k.toNat = c + 1 := ⟨k.toNat - 1, by omega⟩
    have he : 2 * k.toNat - 1 = 2 * c + 1 := by omega
    rw [pentSet, if_pos hpos, he, hc]
    obtain ⟨h1, h2, h3⟩ := Icc_facts (a := c + 1) (b := 2 * c + 1) (by omega) (by omega)
    exact Or.inl ⟨by omega, by omega⟩
  · have hj : 1 ≤ k.natAbs := by omega
    rw [pentSet, if_neg (by omega)]
    obtain ⟨h1, h2, h3⟩ := Icc_facts (a := k.natAbs + 1) (b := 2 * k.natAbs) (by omega) (by omega)
    exact Or.inr ⟨by omega, by omega⟩

theorem pentSet_mem_DPart {k : ℤ} {n : ℕ} (hk : k * (3 * k - 1) = 2 * (n : ℤ)) :
    pentSet k ∈ DPart n := by
  rw [mem_DPart]
  constructor
  · intro hmem
    rcases lt_or_ge 0 k with hpos | hneg
    · rw [pentSet, if_pos hpos] at hmem
      simp only [mem_Icc] at hmem
      omega
    · rw [pentSet, if_neg (by omega)] at hmem
      simp only [mem_Icc] at hmem
      omega
  · have h := sum_pentSet_mul_two k
    rw [hk] at h
    have : ((∑ i ∈ pentSet k, i : ℕ) : ℤ) = (n : ℤ) := by linarith
    exact_mod_cast this

/-- The index of a generalized pentagonal number is unique. -/
theorem pent_index_inj {k l : ℤ} (h : k * (3 * k - 1) = l * (3 * l - 1)) : k = l := by
  have hfac : (k - l) * (3 * (k + l) - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1 <;> omega

theorem exceptional_eq {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) (hn : 1 ≤ n)
    (hexc : Exceptional S) :
    ∃ k : ℤ, k * (3 * k - 1) = 2 * (n : ℤ) ∧ -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) ∧ S = pentSet k := by
  obtain ⟨h0, hsum, hne, hm1, hmM, hr1, hrM⟩ := DPart_facts hS hn
  have hmem : mx S + 1 - runLen S ∈ S := runLen_subset (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hmle := mn_le hmem
  rcases hexc with ⟨hA, hlt⟩ | ⟨hB, heq⟩
  · -- `S = {m, …, 2m-1}`
    have hkey : mx S + 1 - runLen S = mn S := by omega
    have hM2 : mx S + 1 = 2 * mn S := by omega
    have hSeq : S = Finset.Icc (mn S) (mx S) := by
      refine Finset.Subset.antisymm (fun x hx => mem_Icc.mpr ⟨mn_le hx, le_mx hx⟩) ?_
      intro x hx
      exact runLen_subset (by rw [hkey]; exact hx)
    have htn : ((mn S : ℤ)).toNat = mn S := Int.toNat_natCast _
    have hpent : S = pentSet (mn S : ℤ) := by
      rw [pentSet, if_pos (by omega), htn]
      conv_lhs => rw [hSeq]
      congr 1
      omega
    refine ⟨(mn S : ℤ), ?_, ?_, ?_, hpent⟩
    · have h := sum_pentSet_mul_two (mn S : ℤ)
      rw [← hpent, hsum] at h
      linarith
    · omega
    · have h := sum_pentSet_mul_two (mn S : ℤ)
      rw [← hpent, hsum] at h
      nlinarith [h, (by exact_mod_cast hm1 : (1 : ℤ) ≤ (mn S : ℤ))]
  · -- `S = {r+1, …, 2r}`
    have hSeq : S = Finset.Icc (runLen S + 1) (2 * runLen S) := by
      refine Finset.Subset.antisymm (fun x hx => ?_) ?_
      · have h1 := mn_le hx
        have h2 := le_mx hx
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro x hx
        simp only [mem_Icc] at hx
        exact runLen_subset (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hna : (-(runLen S : ℤ)).natAbs = runLen S := by simp
    have hpent : S = pentSet (-(runLen S : ℤ)) := by
      rw [pentSet, if_neg (by omega), hna]
      exact hSeq
    refine ⟨-(runLen S : ℤ), ?_, ?_, ?_, hpent⟩
    · have h := sum_pentSet_mul_two (-(runLen S : ℤ))
      rw [← hpent, hsum] at h
      linarith
    · have h := sum_pentSet_mul_two (-(runLen S : ℤ))
      rw [← hpent, hsum] at h
      nlinarith [h, (by exact_mod_cast hr1 : (1 : ℤ) ≤ (runLen S : ℤ))]
    · omega

theorem sum_exceptional (n : ℕ) (hn : 1 ≤ n) :
    ∑ S ∈ (DPart n).filter Exceptional, (-1 : ℤ) ^ S.card = pentCoeff n := by
  rw [pentCoeff, ← Finset.sum_filter]
  refine (Finset.sum_bij (fun k _ => pentSet k) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [zero_mul] at hk
      have := hk.2
      omega
    exact ⟨pentSet_mem_DPart hk.2, pentSet_exceptional hk0⟩
  · intro k hk l hl _
    rw [Finset.mem_filter] at hk hl
    exact pent_index_inj (by rw [hk.2, hl.2])
  · intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exceptional_eq hS.1 hn hS.2
    exact ⟨k, Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨hk2, hk3⟩, hk1⟩, hk4.symm⟩
  · intro k _
    rw [pentSet_card]

/-! ## The pentagonal number theorem -/

theorem DPart_zero : DPart 0 = {∅} := by
  ext S
  rw [mem_DPart, Finset.mem_singleton]
  constructor
  · rintro ⟨h0, hsum⟩
    rw [Finset.sum_eq_zero_iff] at hsum
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    exact h0 (hsum x hx ▸ hx)
  · rintro rfl
    simp

theorem sum_DPart (n : ℕ) : ∑ S ∈ DPart n, (-1 : ℤ) ^ S.card = pentCoeff n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [DPart_zero, pentCoeff]
    decide
  · rw [← Finset.sum_filter_add_sum_filter_not (DPart n) Exceptional,
      sum_exceptional n hn, sum_nonExceptional n hn, add_zero]

end Pentagonal

import RequestProject.Pentagonal.Franklin

/-!
# The generating function form of Euler's pentagonal number theorem

Combining Franklin's involution (`Pentagonal.sum_DPart`) with Mathlib's generating function
machinery for partitions, we prove that the generating function of the partition numbers is
the inverse of `∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}`.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Pentagonal

/-- The character selecting partitions into distinct parts, with the sign
`(-1)^(number of parts)`. -/
def sgnChar : ℕ → ℕ → ℤ := fun _ c => if c = 1 then -1 else 0

/-- The finite set `S` (of distinct positive parts) viewed as a partition of `n`. -/
noncomputable def toPartition (n : ℕ) (S : Finset ℕ) : n.Partition :=
  if h : 0 ∉ S ∧ ∑ i ∈ S, i = n then
    { parts := S.val
      parts_pos := fun {i} hi => Nat.pos_of_ne_zero fun e => h.1 (e ▸ hi)
      parts_sum := by
        rw [← h.2, Finset.sum]
        simp }
  else Nat.Partition.indiscrete n

theorem toPartition_parts {n : ℕ} {S : Finset ℕ} (hS : S ∈ DPart n) :
    (toPartition n S).parts = S.val := by
  rw [toPartition, dif_pos (mem_DPart.mp hS)]

/-- If the signed character does not vanish on a partition, its parts are distinct. -/
theorem nodup_of_prod_ne_zero {n : ℕ} {p : n.Partition}
    (hne : p.parts.toFinsupp.prod sgnChar ≠ 0) : p.parts.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  by_cases ha : a ∈ p.parts
  · by_contra hcount
    refine hne (Finset.prod_eq_zero (i := a) (by simpa using ha) ?_)
    simp only [sgnChar, Multiset.toFinsupp_apply]
    rw [if_neg (by omega)]
  · simp [Multiset.count_eq_zero_of_notMem ha]

/-- A partition into distinct parts, viewed as a finite set. -/
theorem toFinset_mem_DPart {n : ℕ} {p : n.Partition} (h : p.parts.Nodup) :
    p.parts.toFinset ∈ DPart n := by
  rw [mem_DPart]
  refine ⟨fun h0 => absurd (p.parts_pos (Multiset.mem_toFinset.mp h0)) (lt_irrefl 0), ?_⟩
  rw [Finset.sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr h]
  simpa using p.parts_sum

theorem toPartition_toFinset {n : ℕ} {p : n.Partition} (h : p.parts.Nodup) :
    toPartition n p.parts.toFinset = p := by
  rw [toPartition, dif_pos (mem_DPart.mp (toFinset_mem_DPart h))]
  ext1
  simp only
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr h]

/-- The signed generating function has the expected coefficients. -/
theorem coeff_genFun_sgnChar (n : ℕ) :
    (Nat.Partition.genFun sgnChar).coeff n = ∑ S ∈ DPart n, (-1 : ℤ) ^ S.card := by
  rw [Nat.Partition.coeff_genFun]
  refine (Finset.sum_of_injOn (toPartition n) ?_ (fun S _ => Finset.mem_univ _) ?_ ?_).symm
  · intro S hS T hT hST
    apply Finset.val_injective
    rw [← toPartition_parts (by simpa using hS), ← toPartition_parts (by simpa using hT), hST]
  · intro p _ hp
    by_contra hne
    have hnodup := nodup_of_prod_ne_zero hne
    exact hp ⟨p.parts.toFinset, Finset.mem_coe.mpr (toFinset_mem_DPart hnodup),
      toPartition_toFinset hnodup⟩
  · intro S hS
    rw [Finsupp.prod, Multiset.toFinsupp_support, toPartition_parts hS]
    have hval : Multiset.toFinset S.val = S := by ext x; simp
    rw [hval, Finset.prod_congr rfl (g := fun _ => (-1 : ℤ)) ?_, Finset.prod_const]
    intro x hx
    simp only [sgnChar, Multiset.toFinsupp_apply]
    rw [if_pos (Multiset.count_eq_one_of_mem S.nodup hx)]

theorem coeff_genFun_sgnChar_eq_pentCoeff (n : ℕ) :
    (Nat.Partition.genFun sgnChar).coeff n = pentCoeff n := by
  rw [coeff_genFun_sgnChar, sum_DPart]

theorem genFun_sgnChar_eq : Nat.Partition.genFun sgnChar = PowerSeries.mk pentCoeff := by
  ext n
  rw [coeff_genFun_sgnChar_eq_pentCoeff, PowerSeries.coeff_mk]

/-- The generating function of the partition numbers. -/
theorem genFun_one_eq :
    Nat.Partition.genFun (fun _ _ => (1 : ℤ)) =
      PowerSeries.mk fun n => (Fintype.card n.Partition : ℤ) := by
  ext n
  rw [Nat.Partition.coeff_genFun, PowerSeries.coeff_mk]
  simp only [Finsupp.prod, Finset.prod_const_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-! ## The infinite products -/

theorem hasProd_sgnChar :
    HasProd (fun i => 1 - (X : ℤ⟦X⟧) ^ (i + 1)) (Nat.Partition.genFun sgnChar) := by
  have h := Nat.Partition.hasProd_genFun sgnChar
  convert h using 2 with i
  have : ∑' j : ℕ, sgnChar (i + 1) (j + 1) • (X : ℤ⟦X⟧) ^ ((i + 1) * (j + 1)) =
      -(X : ℤ⟦X⟧) ^ (i + 1) := by
    rw [tsum_eq_single 0 ?_]
    · simp [sgnChar]
    · intro j hj
      simp [sgnChar, hj]
  rw [this]
  ring

theorem hasProd_one_char :
    HasProd (fun i => ∑' j : ℕ, ((X : ℤ⟦X⟧) ^ (i + 1)) ^ j)
      (Nat.Partition.genFun (fun _ _ => (1 : ℤ))) := by
  have h := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ))
  convert h using 2 with i
  have hc : ((X : ℤ⟦X⟧) ^ (i + 1)).constantCoeff = 0 := by
    simp
  have hsummable : Summable (fun j : ℕ => ((X : ℤ⟦X⟧) ^ (i + 1)) ^ j) :=
    WithPiTopology.summable_pow_of_constantCoeff_eq_zero hc
  rw [hsummable.tsum_eq_zero_add]
  simp only [pow_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← pow_mul, one_smul]

theorem factor_mul_eq_one (i : ℕ) :
    (1 - (X : ℤ⟦X⟧) ^ (i + 1)) * (∑' j : ℕ, ((X : ℤ⟦X⟧) ^ (i + 1)) ^ j) = 1 := by
  refine WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero ?_
  simp

theorem genFun_mul_eq_one :
    Nat.Partition.genFun sgnChar * Nat.Partition.genFun (fun _ _ => (1 : ℤ)) = 1 := by
  have h := hasProd_sgnChar.mul hasProd_one_char
  simp only [factor_mul_eq_one] at h
  exact h.unique hasProd_one

/-- **Euler's pentagonal number theorem** for the partition generating function. -/
theorem euler_pentagonal :
    (PowerSeries.mk fun n => (Fintype.card n.Partition : ℤ)) *
      (PowerSeries.mk pentCoeff) = 1 := by
  rw [← genFun_one_eq, ← genFun_sgnChar_eq, mul_comm]
  exact genFun_mul_eq_one

end Pentagonal

