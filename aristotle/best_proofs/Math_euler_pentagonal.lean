import Mathlib
import RequestProject.Pentagonal

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

`Math.euler_pentagonal` states the identity of formal power series over `ℤ`
$$\prod_{n = 1}^{\infty} (1 - X^n) = \sum_{k \in \mathbb Z} (-1)^k X^{k(3k-1)/2},$$
where the product and the sum are taken in the `X`-adic (product) topology on `ℤ⟦X⟧`.

`Math.euler_pentagonal_partition` states the corresponding statement for the generating
function of the partition function: the pentagonal series is the multiplicative inverse of
$\sum_{n} p(n) X^n$.

The combinatorial heart of the proof (Franklin's involution) is in
`RequestProject.Pentagonal`.
-/

namespace Math

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology

/-- The pentagonal exponent `k(3k-1)/2`. -/
abbrev pentExp : ℤ → ℕ := Franklin.pentExp

/-- The sign `(-1)^k`. -/
abbrev pentSign : ℤ → ℤ := Franklin.pentSign

/-- The pentagonal series `∑_{k ∈ ℤ} (-1)^k X^{k(3k-1)/2}` as a formal power series over `ℤ`. -/
noncomputable def pentagonalSeries : ℤ⟦X⟧ :=
  ∑' k : ℤ, pentSign k • (X : ℤ⟦X⟧) ^ pentExp k

/-! ### Expanding a finite product -/

theorem prod_one_sub_X_pow_expand (s : Finset ℕ) :
    ∏ i ∈ s, ((1 : ℤ⟦X⟧) - X ^ (i + 1))
      = ∑ t ∈ s.powerset, ((-1 : ℤ) ^ (#t)) • X ^ (∑ i ∈ t, (i + 1)) := by
  have h := Finset.prod_add (fun i : ℕ => -((X : ℤ⟦X⟧) ^ (i + 1))) (fun _ => (1 : ℤ⟦X⟧)) s
  simp only [mul_one, Finset.prod_const_one] at h
  rw [show (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (i + 1)) = (fun i : ℕ => -((X : ℤ⟦X⟧) ^ (i + 1)) + 1) by
    funext i; ring]
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_neg, Finset.prod_pow_eq_pow_sum, zsmul_eq_mul]
  push_cast
  ring

theorem coeff_prod_one_sub_X_pow (d : ℕ) (s : Finset ℕ) :
    (PowerSeries.coeff d) (∏ i ∈ s, ((1 : ℤ⟦X⟧) - X ^ (i + 1)))
      = ∑ t ∈ s.powerset.filter (fun t => ∑ i ∈ t, (i + 1) = d), (-1 : ℤ) ^ (#t) := by
  rw [prod_one_sub_X_pow_expand, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, coeff_X_pow]
  by_cases h : ∑ i ∈ t, (i + 1) = d
  · simp [h]
  · have h' : ¬ (d = ∑ i ∈ t, (i + 1)) := fun hh => h hh.symm
    simp [h, h']

/-- Subsets of `s` whose shifted sum is `d` are in bijection with the partitions of `d`
into distinct parts. -/
theorem sum_powerset_filter_eq_sum_parts (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    ∑ t ∈ s.powerset.filter (fun t => ∑ i ∈ t, (i + 1) = d), (-1 : ℤ) ^ (#t)
      = ∑ S ∈ Franklin.parts d, (-1 : ℤ) ^ (#S) := by
  have hinj1 : ∀ (t : Finset ℕ), ∀ x ∈ t, ∀ y ∈ t, x + 1 = y + 1 → x = y := by
    intro t x _ y _ h; omega
  refine Finset.sum_nbij' (fun t => t.image (· + 1)) (fun S => S.image (· - 1)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    refine Franklin.mem_parts.2 ⟨by simp, ?_⟩
    rw [Finset.sum_image (fun x hx y hy h => hinj1 t x hx y hy (by simpa using h))]
    exact ht.2
  · intro S hS
    obtain ⟨h0, hsum⟩ := Franklin.mem_parts.1 hS
    have hpos : ∀ x ∈ S, 1 ≤ x := by
      intro x hx
      rcases Nat.eq_zero_or_pos x with rfl | h
      · exact absurd hx h0
      · exact h
    have hle : ∀ x ∈ S, x ≤ d := by
      intro x hx
      have h2 : x ≤ ∑ i ∈ S, i := by
        simpa using Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
      omega
    have hinj2 : ∀ x ∈ S, ∀ y ∈ S, x - 1 = y - 1 → x = y := by
      intro x hx y hy h
      have := hpos x hx
      have := hpos y hy
      simp only at h
      omega
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine hs ?_
      simp only [Finset.mem_range]
      have := hpos x hx
      have := hle x hx
      omega
    · rw [Finset.sum_image (fun x hx y hy h => hinj2 x hx y hy (by simpa using h)), ← hsum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have := hpos x hx
      omega
  · intro t _
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨x + 1, ⟨x, hx, rfl⟩, by omega⟩
  · intro S hS
    obtain ⟨h0, -⟩ := Franklin.mem_parts.1 hS
    have hpos : ∀ x ∈ S, 1 ≤ x := by
      intro x hx
      rcases Nat.eq_zero_or_pos x with rfl | h
      · exact absurd hx h0
      · exact h
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := hpos z hz
      show z - 1 + 1 ∈ S
      rwa [Nat.sub_add_cancel h1]
    · intro hx
      exact ⟨x - 1, ⟨x, hx, rfl⟩, by have := hpos x hx; omega⟩
  · intro t _
    congr 1
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h)]

/-! ### The two sides as explicit power series -/

/-- The infinite product `∏_{n ≥ 1} (1 - X^n)` has the pentagonal coefficients. -/
theorem hasProd_one_sub_X_pow :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (i + 1))
      (PowerSeries.mk fun n => Franklin.pentCoeff n) := by
  rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (i₀ := Finset.range d) (fun s hs ↦ ?_)
  rw [coeff_prod_one_sub_X_pow, sum_powerset_filter_eq_sum_parts d s hs,
    Franklin.sum_parts_eq_pentCoeff, coeff_mk]

/-- The pentagonal series has the pentagonal coefficients. -/
theorem hasSum_pentagonal :
    HasSum (fun k : ℤ => pentSign k • (X : ℤ⟦X⟧) ^ pentExp k)
      (PowerSeries.mk fun n => Franklin.pentCoeff n) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  have hfun : ∀ k : ℤ, (PowerSeries.coeff d) (pentSign k • (X : ℤ⟦X⟧) ^ pentExp k)
      = if pentExp k = d then pentSign k else 0 := by
    intro k
    rw [map_smul, coeff_X_pow]
    by_cases h : pentExp k = d
    · simp [h]
    · have h' : ¬ (d = pentExp k) := fun hh => h hh.symm
      simp [h, h']
  simp only [hfun, coeff_mk, Franklin.pentCoeff]
  refine hasSum_sum_of_ne_finset_zero ?_
  intro k hk
  rw [if_neg]
  intro hpe
  apply hk
  have hle := Franklin.natAbs_le_pentExp k
  rw [show Franklin.pentExp k = d from hpe] at hle
  rw [Finset.mem_Icc]
  omega

theorem pentagonalSeries_eq_mk :
    pentagonalSeries = PowerSeries.mk fun n => Franklin.pentCoeff n :=
  hasSum_pentagonal.tsum_eq

/-! ### Euler's pentagonal number theorem -/

/-- **Euler's pentagonal number theorem**:
`∏_{n ≥ 1} (1 - X^n) = ∑_{k ∈ ℤ} (-1)^k X^{k(3k-1)/2}` as formal power series over `ℤ`. -/
theorem euler_pentagonal :
    ∏' i : ℕ, ((1 : ℤ⟦X⟧) - X ^ (i + 1)) = ∑' k : ℤ, pentSign k • (X : ℤ⟦X⟧) ^ pentExp k := by
  rw [hasProd_one_sub_X_pow.tprod_eq, hasSum_pentagonal.tsum_eq]

/-- The generating function of the partition function `p n`. -/
noncomputable def partitionSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => (Fintype.card n.Partition : ℤ)

theorem hasProd_partitionSeries :
    HasProd (fun i : ℕ => ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) partitionSeries := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ : ℕ => True)
  simp only [if_pos trivial] at h
  have hcard : ∀ n : ℕ, (#(Nat.Partition.restricted n (fun _ : ℕ => True)) : ℤ)
      = (Fintype.card n.Partition : ℤ) := by
    intro n
    congr 1
    rw [Nat.Partition.restricted]
    simp [Finset.filter_true_of_mem, Finset.card_univ]
  simpa [partitionSeries, hcard] using h

/-- **Euler's pentagonal number theorem** for the partition generating function: the pentagonal
series is the inverse of `∑_n p(n) X^n`, where `p n` is the number of partitions of `n`. -/
theorem euler_pentagonal_partition : partitionSeries * pentagonalSeries = 1 := by
  have h1 := hasProd_partitionSeries
  have h2 := hasProd_one_sub_X_pow
  have h3 := h1.mul h2
  have hone : (fun i : ℕ => (∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1)))
      = fun _ : ℕ => (1 : ℤ⟦X⟧) := by
    funext i
    have hc : ((X : ℤ⟦X⟧) ^ (i + 1)).constantCoeff = 0 := by
      simp
    have := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hc
    simpa [pow_mul] using this
  rw [hone] at h3
  have h4 : partitionSeries * (PowerSeries.mk fun n => Franklin.pentCoeff n) = 1 :=
    (hasProd_one.unique h3).symm
  rw [pentagonalSeries_eq_mk]
  exact h4

end Math

import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

We represent a partition of `n` into distinct parts as a `Finset ℕ` of positive integers
summing to `n`.  The main result of this file is
`Franklin.sum_parts_eq_pentCoeff`:
`∑ S ∈ parts n, (-1) ^ #S = pentCoeff n`,
where `pentCoeff n` is the coefficient of `X ^ n` in `∑ k : ℤ, (-1)^k X^(k(3k-1)/2)`.
-/

open Finset

namespace Franklin

/-- The pentagonal exponent `k (3k-1) / 2` of an integer `k`. -/
def pentExp (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

/-- The sign `(-1)^k` attached to the pentagonal number of index `k`. -/
def pentSign (k : ℤ) : ℤ := (-1) ^ k.natAbs

/-- The coefficient of `X ^ n` in the pentagonal series
`∑_{k ∈ ℤ} (-1)^k X^{k(3k-1)/2}`. -/
def pentCoeff (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentExp k = n then pentSign k else 0

/-- Partitions of `n` into distinct (positive) parts, as finsets of naturals. -/
def parts (n : ℕ) : Finset (Finset ℕ) :=
  {S ∈ (Finset.range (n + 1)).powerset | 0 ∉ S ∧ ∑ i ∈ S, i = n}

/-- The smallest part of `S` (junk value `0` if `S = ∅`). -/
noncomputable def lo (S : Finset ℕ) : ℕ := sInf {x | x ∈ S}

/-- The largest part of `S` (junk value `0` if `S = ∅`). -/
def hi (S : Finset ℕ) : ℕ := S.sup id

/-- The length of the maximal "staircase" `hi S, hi S - 1, …` contained in `S`. -/
noncomputable def stair (S : Finset ℕ) : ℕ := sInf {k | hi S - k ∉ S}

/-- The exceptional (fixed point) configurations of Franklin's involution. -/
def Exc (S : Finset ℕ) : Prop :=
  (lo S ≤ stair S ∧ hi S < 2 * lo S) ∨ (stair S < lo S ∧ hi S = 2 * stair S)

noncomputable instance : DecidablePred Exc := Classical.decPred _

/-- Franklin's involution. -/
noncomputable def franklin (S : Finset ℕ) : Finset ℕ :=
  if lo S ≤ stair S then
    ((S.filter (· ≤ hi S - lo S)).erase (lo S)) ∪ Finset.Icc (hi S - lo S + 2) (hi S + 1)
  else
    insert (stair S)
      ((S.filter (· ≤ hi S - stair S)) ∪ Finset.Icc (hi S - stair S) (hi S - 1))

/-- The exceptional finset of index `k`: `{k, …, 2k-1}` for `k > 0`
and `{|k|+1, …, 2|k|}` for `k < 0`. -/
def pentSet (k : ℤ) : Finset ℕ :=
  if 0 ≤ k then Finset.Ico k.toNat (2 * k.toNat)
  else Finset.Ico ((-k).toNat + 1) (2 * (-k).toNat + 1)

/-! ### Basic lemmas -/

variable {S : Finset ℕ} {n : ℕ}

theorem mem_parts {S : Finset ℕ} {n : ℕ} :
    S ∈ parts n ↔ 0 ∉ S ∧ ∑ i ∈ S, i = n := by
  constructor
  · intro h
    simp only [parts, Finset.mem_filter, Finset.mem_powerset] at h
    exact h.2
  · rintro ⟨h0, hsum⟩
    simp only [parts, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, h0, hsum⟩
    intro x hx
    simp only [Finset.mem_range]
    have : x ≤ ∑ i ∈ S, i := Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    omega

theorem lo_mem (h : S.Nonempty) : lo S ∈ S := Nat.sInf_mem h

theorem lo_le {x : ℕ} (hx : x ∈ S) : lo S ≤ x := Nat.sInf_le hx

theorem hi_mem (h : S.Nonempty) : hi S ∈ S := by
  have : S.sup id = S.max' h := by rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
  rw [hi, this]
  exact S.max'_mem h

theorem le_hi {x : ℕ} (hx : x ∈ S) : x ≤ hi S := Finset.le_sup (f := id) hx

theorem stair_lt_mem {j : ℕ} (hj : j < stair S) : hi S - j ∈ S := by
  simpa using Nat.notMem_of_lt_sInf hj

theorem stair_setNonempty (h0 : 0 ∉ S) : {k | hi S - k ∉ S}.Nonempty :=
  ⟨hi S, by simpa using h0⟩

theorem stair_notMem (h0 : 0 ∉ S) : hi S - stair S ∉ S := Nat.sInf_mem (stair_setNonempty h0)

theorem stair_eq {r : ℕ} (h1 : ∀ j < r, hi S - j ∈ S) (h2 : hi S - r ∉ S) : stair S = r := by
  have hne : {k | hi S - k ∉ S}.Nonempty := ⟨r, h2⟩
  refine le_antisymm (Nat.sInf_le h2) ?_
  by_contra hlt
  push_neg at hlt
  exact (Nat.sInf_mem hne) (h1 _ hlt)

theorem le_stair (h0 : 0 ∉ S) {r : ℕ} (h : ∀ j < r, hi S - j ∈ S) : r ≤ stair S := by
  by_contra hlt
  push_neg at hlt
  exact (stair_notMem h0) (h _ hlt)

theorem stair_pos (h0 : 0 ∉ S) (h : S.Nonempty) : 0 < stair S := by
  refine Nat.pos_of_ne_zero fun hz => ?_
  have hmem := stair_notMem h0
  rw [hz, Nat.sub_zero] at hmem
  exact hmem (hi_mem h)

theorem lo_pos (h0 : 0 ∉ S) (h : S.Nonempty) : 0 < lo S := by
  rcases Nat.eq_zero_or_pos (lo S) with hz | hp
  · exact absurd (hz ▸ lo_mem h) h0
  · exact hp

/-- The top `r` elements of `S` form the interval `Icc (hi S - r + 1) (hi S)`. -/
theorem staircase_subset {r : ℕ} (hr : r ≤ stair S) :
    Finset.Icc (hi S - r + 1) (hi S) ⊆ S := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  have hj : hi S - x < r := by omega
  have hmem := stair_lt_mem (S := S) (lt_of_lt_of_le hj hr)
  have heq : hi S - (hi S - x) = x := by omega
  rwa [heq] at hmem

theorem filter_gt_eq {r : ℕ} (hr : r ≤ stair S) :
    S.filter (fun x => hi S - r < x) = Finset.Icc (hi S - r + 1) (hi S) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hxS, hx⟩
    exact ⟨by omega, le_hi hxS⟩
  · rintro ⟨h1, h2⟩
    exact ⟨staircase_subset hr (Finset.mem_Icc.2 ⟨h1, h2⟩), by omega⟩

theorem decomp {r : ℕ} (hr : r ≤ stair S) :
    S = S.filter (fun x => x ≤ hi S - r) ∪ Finset.Icc (hi S - r + 1) (hi S) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hx
    by_cases h : x ≤ hi S - r
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨by omega, le_hi hx⟩
  · rintro (⟨hx, _⟩ | ⟨h1, h2⟩)
    · exact hx
    · exact staircase_subset hr (Finset.mem_Icc.2 ⟨h1, h2⟩)

theorem decomp_disjoint {r : ℕ} :
    Disjoint (S.filter (fun x => x ≤ hi S - r)) (Finset.Icc (hi S - r + 1) (hi S)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_filter] at hx
  simp only [Finset.mem_Icc] at hx'
  omega

theorem sum_Icc_succ (a b : ℕ) :
    ∑ i ∈ Finset.Icc (a + 1) (b + 1), i = (∑ i ∈ Finset.Icc a b, i) + #(Finset.Icc a b) := by
  rw [← map_add_right_Icc a b 1, Finset.sum_map]
  simp [Finset.sum_add_distrib, addRightEmbedding]

/-! ### The first branch of Franklin's involution -/

/-- If the smallest part is at most the length of the top staircase (and the configuration is
not exceptional), Franklin's map removes the smallest part and enlarges the staircase. -/
theorem caseA {n : ℕ} {S : Finset ℕ} (hS : S ∈ parts n) (hne : S.Nonempty)
    (hst : lo S ≤ stair S) (hMs : 2 * lo S ≤ hi S) :
    franklin S ∈ parts n ∧ (franklin S).Nonempty ∧ hi (franklin S) = hi S + 1 ∧
      stair (franklin S) = lo S ∧ lo S < lo (franklin S) ∧
      #(franklin S) + 1 = #S ∧ franklin (franklin S) = S := by
  obtain ⟨h0, hsum⟩ := mem_parts.1 hS
  set s := lo S with hs
  set M := hi S with hM
  set low := S.filter (fun x => x ≤ M - s) with hlow
  have hs1 : 1 ≤ s := lo_pos h0 hne
  have hsS : s ∈ S := lo_mem hne
  have hsM : s ≤ M := le_hi hsS
  have hsMs : s ≤ M - s := by omega
  have hslow : s ∈ low := by simp [hlow, hsS, hsMs]
  have hT : franklin S = low.erase s ∪ Finset.Icc (M - s + 2) (M + 1) := by
    rw [franklin, if_pos hst]
  have hTmem : ∀ x, x ∈ franklin S ↔
      ((x ∈ S ∧ x ≤ M - s) ∧ x ≠ s) ∨ (M - s + 2 ≤ x ∧ x ≤ M + 1) := by
    intro x
    rw [hT]
    simp [hlow, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc, and_comm]
  have hdec : S = low ∪ Finset.Icc (M - s + 1) M := decomp hst
  have hdisj : Disjoint low (Finset.Icc (M - s + 1) M) := decomp_disjoint
  have hcardIcc : #(Finset.Icc (M - s + 1) M) = s := by rw [Nat.card_Icc]; omega
  have hcardS : #S = #low + s := by
    conv_lhs => rw [hdec]
    rw [Finset.card_union_of_disjoint hdisj, hcardIcc]
  have hsumS : ∑ i ∈ S, i = (∑ i ∈ low, i) + ∑ i ∈ Finset.Icc (M - s + 1) M, i := by
    conv_lhs => rw [hdec]
    rw [Finset.sum_union hdisj]
  have hdisjT : Disjoint (low.erase s) (Finset.Icc (M - s + 2) (M + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_erase, hlow, Finset.mem_filter] at hx
    simp only [Finset.mem_Icc] at hx'
    omega
  have hcardT : #(franklin S) + 1 = #S := by
    rw [hT, Finset.card_union_of_disjoint hdisjT, Finset.card_erase_of_mem hslow, Nat.card_Icc,
      hcardS]
    have : 1 ≤ #low := Finset.card_pos.2 ⟨s, hslow⟩
    omega
  have hsumT : ∑ i ∈ franklin S, i = n := by
    rw [hT, Finset.sum_union hdisjT]
    have h1 : (∑ i ∈ low.erase s, i) + s = ∑ i ∈ low, i := Finset.sum_erase_add _ _ hslow
    have h2 : ∑ i ∈ Finset.Icc (M - s + 2) (M + 1), i
        = (∑ i ∈ Finset.Icc (M - s + 1) M, i) + s := by
      have h3 := sum_Icc_succ (M - s + 1) M
      rw [hcardIcc] at h3
      have e1 : M - s + 1 + 1 = M - s + 2 := by omega
      rw [e1] at h3
      exact h3
    omega
  have hmemTop : (M + 1) ∈ franklin S := by rw [hTmem]; right; omega
  have hTne : (franklin S).Nonempty := ⟨M + 1, hmemTop⟩
  have hT0 : 0 ∉ franklin S := by
    rw [hTmem]
    rintro (⟨⟨hx, _⟩, _⟩ | ⟨h1, h2⟩)
    · exact h0 hx
    · omega
  have hhiT : hi (franklin S) = M + 1 := by
    refine le_antisymm ?_ (le_hi hmemTop)
    refine Finset.sup_le ?_
    intro x hx
    rw [hTmem] at hx
    rcases hx with ⟨⟨hx, hx2⟩, _⟩ | ⟨h1, h2⟩
    · simp only [id]; omega
    · simpa using h2
  have hloT : s < lo (franklin S) := by
    have hmem := lo_mem hTne
    rw [hTmem] at hmem
    rcases hmem with ⟨⟨hx, hx2⟩, hne'⟩ | ⟨h1, h2⟩
    · have := lo_le (S := S) hx
      omega
    · omega
  have hstairT : stair (franklin S) = s := by
    refine stair_eq ?_ ?_
    · intro j hj
      rw [hhiT, hTmem]
      right; omega
    · rw [hhiT, hTmem]
      rintro (⟨⟨hx, hx2⟩, hne'⟩ | ⟨h1, h2⟩) <;> omega
  have hstair : Finset.Icc (M - s + 1) M ⊆ S := staircase_subset hst
  have hfr : franklin (franklin S) = S := by
    rw [franklin, if_neg (by omega), hstairT, hhiT]
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, hTmem]
    constructor
    · rintro (rfl | ⟨(⟨⟨hx, _⟩, _⟩ | ⟨ha, hb⟩), hle⟩ | ⟨h1, h2⟩)
      · exact hsS
      · exact hx
      · omega
      · exact hstair (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    · intro hx
      have hxM : x ≤ M := le_hi hx
      by_cases hxs : x = s
      · exact Or.inl hxs
      · by_cases hle : x ≤ M - s
        · exact Or.inr (Or.inl ⟨Or.inl ⟨⟨hx, hle⟩, hxs⟩, by omega⟩)
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  exact ⟨mem_parts.2 ⟨hT0, hsumT⟩, hTne, hhiT, hstairT, hloT, hcardT, hfr⟩

/-! ### The second branch of Franklin's involution -/

/-- If the top staircase is shorter than the smallest part (and the configuration is not
exceptional), Franklin's map shrinks the staircase and inserts a new smallest part. -/
theorem caseB {n : ℕ} {S : Finset ℕ} (hS : S ∈ parts n) (hne : S.Nonempty)
    (hst : stair S < lo S) (hMne : hi S ≠ 2 * stair S) :
    franklin S ∈ parts n ∧ (franklin S).Nonempty ∧ hi (franklin S) = hi S - 1 ∧
      lo (franklin S) = stair S ∧ lo (franklin S) ≤ stair (franklin S) ∧
      2 * lo (franklin S) ≤ hi (franklin S) ∧
      #S + 1 = #(franklin S) ∧ franklin (franklin S) = S := by
  obtain ⟨h0, hsum⟩ := mem_parts.1 hS
  set s := lo S with hs
  set M := hi S with hM
  set t := stair S with hts
  set low := S.filter (fun x => x ≤ M - t) with hlow
  have ht1 : 1 ≤ t := stair_pos h0 hne
  have hsS : s ∈ S := lo_mem hne
  have hsM : s ≤ M := le_hi hsS
  have hstair : Finset.Icc (M - t + 1) M ⊆ S := staircase_subset le_rfl
  have hMt1 : M - t + 1 ∈ S := hstair (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hsle : s ≤ M - t + 1 := lo_le hMt1
  have hMbig : 2 * t + 1 ≤ M := by omega
  have hMtnot : M - t ∉ S := stair_notMem h0
  have hlowlt : ∀ x ∈ low, x ∈ S ∧ x ≤ M - t - 1 := by
    intro x hx
    simp only [hlow, Finset.mem_filter] at hx
    refine ⟨hx.1, ?_⟩
    rcases Nat.lt_or_ge x (M - t) with h | h
    · omega
    · have hxe : x = M - t := by omega
      exact absurd (hxe ▸ hx.1) hMtnot
  have hT : franklin S = insert t (low ∪ Finset.Icc (M - t) (M - 1)) := by
    rw [franklin, if_neg (by omega)]
  have hTmem : ∀ x, x ∈ franklin S ↔
      x = t ∨ (x ∈ S ∧ x ≤ M - t) ∨ (M - t ≤ x ∧ x ≤ M - 1) := by
    intro x
    rw [hT]
    simp [hlow, Finset.mem_insert, Finset.mem_union, Finset.mem_Icc]
  have hdisj2 : Disjoint low (Finset.Icc (M - t) (M - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := hlowlt x hx
    simp only [Finset.mem_Icc] at hx'
    omega
  have hcardIcc2 : #(Finset.Icc (M - t) (M - 1)) = t := by rw [Nat.card_Icc]; omega
  have hcardIcc : #(Finset.Icc (M - t + 1) M) = t := by rw [Nat.card_Icc]; omega
  have hdec : S = low ∪ Finset.Icc (M - t + 1) M := decomp le_rfl
  have hdisj : Disjoint low (Finset.Icc (M - t + 1) M) := decomp_disjoint
  have hcardS : #S = #low + t := by
    conv_lhs => rw [hdec]
    rw [Finset.card_union_of_disjoint hdisj, hcardIcc]
  have hsumS : ∑ i ∈ S, i = (∑ i ∈ low, i) + ∑ i ∈ Finset.Icc (M - t + 1) M, i := by
    conv_lhs => rw [hdec]
    rw [Finset.sum_union hdisj]
  have htnot : t ∉ low ∪ Finset.Icc (M - t) (M - 1) := by
    intro hmem
    rcases Finset.mem_union.1 hmem with h | h
    · have h1 := hlowlt t h
      have := lo_le (S := S) h1.1
      omega
    · simp only [Finset.mem_Icc] at h; omega
  have hcardT : #S + 1 = #(franklin S) := by
    rw [hT, Finset.card_insert_of_notMem htnot, Finset.card_union_of_disjoint hdisj2, hcardIcc2,
      hcardS]
  have hsumT : ∑ i ∈ franklin S, i = n := by
    rw [hT, Finset.sum_insert htnot, Finset.sum_union hdisj2]
    have h2 : ∑ i ∈ Finset.Icc (M - t + 1) M, i
        = (∑ i ∈ Finset.Icc (M - t) (M - 1), i) + t := by
      have h3 := sum_Icc_succ (M - t) (M - 1)
      rw [hcardIcc2] at h3
      have e1 : M - 1 + 1 = M := by omega
      rw [e1] at h3
      exact h3
    omega
  have htT : t ∈ franklin S := by rw [hTmem]; left; rfl
  have hTne : (franklin S).Nonempty := ⟨t, htT⟩
  have hTge : ∀ x ∈ franklin S, t ≤ x := by
    intro x hx
    rw [hTmem] at hx
    rcases hx with rfl | ⟨hxS, hle⟩ | ⟨h1, h2⟩
    · exact le_rfl
    · have := lo_le (S := S) hxS; omega
    · omega
  have hT0 : 0 ∉ franklin S := fun hmem => by have := hTge 0 hmem; omega
  have hmemTop : (M - 1) ∈ franklin S := by rw [hTmem]; right; right; omega
  have hhiT : hi (franklin S) = M - 1 := by
    refine le_antisymm (Finset.sup_le ?_) (le_hi hmemTop)
    intro x hx
    rw [hTmem] at hx
    simp only [id]
    rcases hx with rfl | ⟨hxS, hle⟩ | ⟨h1, h2⟩
    · omega
    · have : x ≠ M - t := fun he => hMtnot (he ▸ hxS)
      omega
    · omega
  have hloT : lo (franklin S) = t := le_antisymm (lo_le htT) (hTge _ (lo_mem hTne))
  have hstairT : t ≤ stair (franklin S) := by
    refine le_stair hT0 ?_
    intro j hj
    rw [hhiT, hTmem]
    right; right; omega
  have hfr : franklin (franklin S) = S := by
    rw [franklin, if_pos (by omega), hloT, hhiT]
    ext x
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc, hTmem]
    constructor
    · rintro (⟨hxt, (rfl | ⟨hxS, hle⟩ | ⟨ha, hb⟩), hle2⟩ | ⟨h1, h2⟩)
      · omega
      · exact hxS
      · omega
      · exact hstair (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    · intro hx
      have hxM : x ≤ M := le_hi hx
      have hxs : t < x := lt_of_lt_of_le hst (lo_le hx)
      have hxne : x ≠ M - t := fun he => hMtnot (he ▸ hx)
      by_cases hle : x ≤ M - t
      · exact Or.inl ⟨by omega, Or.inr (Or.inl ⟨hx, hle⟩), by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
  exact ⟨mem_parts.2 ⟨hT0, hsumT⟩, hTne, hhiT, hloT, by omega, by omega, hcardT, hfr⟩

/-! ### The involution kills all non-exceptional configurations -/

theorem franklin_props {n : ℕ} {S : Finset ℕ} (hS : S ∈ parts n) (hne : S.Nonempty)
    (hexc : ¬ Exc S) :
    franklin S ∈ parts n ∧ (franklin S).Nonempty ∧ ¬ Exc (franklin S) ∧
      (-1 : ℤ) ^ #S + (-1) ^ #(franklin S) = 0 ∧ franklin (franklin S) = S := by
  rw [Exc] at hexc
  push_neg at hexc
  by_cases h : lo S ≤ stair S
  · have hMs : 2 * lo S ≤ hi S := by have := hexc.1 h; omega
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := caseA hS hne h hMs
    refine ⟨h1, h2, ?_, ?_, h7⟩
    · rw [Exc]; push_neg
      exact ⟨fun hle => by omega, fun hlt => by omega⟩
    · have he : #S = #(franklin S) + 1 := by omega
      rw [he, pow_succ]; ring
  · push_neg at h
    have hMne : hi S ≠ 2 * stair S := hexc.2 h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := caseB hS hne h hMne
    refine ⟨h1, h2, ?_, ?_, h8⟩
    · rw [Exc]; push_neg
      exact ⟨fun hle => by omega, fun hlt => by omega⟩
    · have he : #(franklin S) = #S + 1 := by omega
      rw [he, pow_succ]; ring

theorem nonempty_of_mem_parts {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : S ∈ parts n) :
    S.Nonempty := by
  rcases Finset.eq_empty_or_nonempty S with rfl | h
  · exfalso
    have := (mem_parts.1 hS).2
    simp only [Finset.sum_empty] at this
    omega
  · exact h

theorem sum_parts_eq_sum_exc {n : ℕ} (hn : 0 < n) :
    ∑ S ∈ parts n, (-1 : ℤ) ^ #S = ∑ S ∈ (parts n).filter Exc, (-1 : ℤ) ^ #S := by
  rw [← Finset.sum_filter_add_sum_filter_not (parts n) Exc]
  have hmemiff : ∀ S, S ∈ (parts n).filter (fun S => ¬ Exc S) ↔ S ∈ parts n ∧ ¬ Exc S := by
    intro S; simp [Finset.mem_filter]
  have hzero : ∑ S ∈ (parts n).filter (fun S => ¬ Exc S), (-1 : ℤ) ^ #S = 0 := by
    refine Finset.sum_involution (fun S _ => franklin S) ?_ ?_ ?_ ?_
    · intro S hSmem
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      exact (franklin_props hS (nonempty_of_mem_parts hn hS) hexc).2.2.2.1
    · intro S hSmem _
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      intro hcon
      have hcon' : franklin S = S := hcon
      have hsign := (franklin_props hS (nonempty_of_mem_parts hn hS) hexc).2.2.2.1
      rw [hcon'] at hsign
      have hne0 : ((-1 : ℤ)) ^ #S ≠ 0 := by positivity
      omega
    · intro S hSmem
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      obtain ⟨h1, h2, h3, h4, h5⟩ := franklin_props hS (nonempty_of_mem_parts hn hS) hexc
      exact (hmemiff _).2 ⟨h1, h3⟩
    · intro S hSmem
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      exact (franklin_props hS (nonempty_of_mem_parts hn hS) hexc).2.2.2.2
  rw [hzero, add_zero]

/-! ### The exceptional configurations are the pentagonal ones -/

theorem Ico_facts {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    0 ∉ Finset.Ico a b ∧ lo (Finset.Ico a b) = a ∧ hi (Finset.Ico a b) = b - 1 ∧
      stair (Finset.Ico a b) = b - a := by
  have hmem : ∀ x, x ∈ Finset.Ico a b ↔ a ≤ x ∧ x < b := by intro x; simp
  have h0 : 0 ∉ Finset.Ico a b := by rw [hmem]; omega
  have hane : (Finset.Ico a b).Nonempty := ⟨a, by rw [hmem]; omega⟩
  have hlo : lo (Finset.Ico a b) = a := by
    refine le_antisymm (lo_le (by rw [hmem]; omega)) ?_
    have := lo_mem hane
    rw [hmem] at this
    omega
  have hhi : hi (Finset.Ico a b) = b - 1 := by
    refine le_antisymm (Finset.sup_le ?_) (le_hi (by rw [hmem]; omega))
    intro x hx
    rw [hmem] at hx
    simp only [id]
    omega
  refine ⟨h0, hlo, hhi, ?_⟩
  refine stair_eq ?_ ?_ <;> rw [hhi]
  · intro j hj
    rw [hmem]; omega
  · rw [hmem]; omega

theorem stair_le_hi {S : Finset ℕ} (h0 : 0 ∉ S) : stair S ≤ hi S :=
  Nat.sInf_le (by simpa using h0)

theorem pentExp_spec (k : ℤ) : 2 * (pentExp k : ℤ) = k * (3 * k - 1) := by
  have heven : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with h | h
    · obtain ⟨m, rfl⟩ := h; exact ⟨m * (3 * (m + m) - 1), by ring⟩
    · obtain ⟨m, rfl⟩ := h; exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
  have hnonneg : 0 ≤ k * (3 * k - 1) := by nlinarith [sq_nonneg k, sq_nonneg (k - 1)]
  rw [pentExp, Int.toNat_of_nonneg (Int.ediv_nonneg hnonneg (by norm_num))]
  exact Int.mul_ediv_cancel' heven

theorem sum_Ico_two_mul (m : ℕ) : 2 * (∑ i ∈ Finset.Ico m (2 * m), i) + m = 3 * m ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * m - m = m := by omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  have h2 := Finset.sum_range_id_mul_two m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp only [Nat.succ_sub_one] at h2
    simp only [smul_eq_mul]
    nlinarith [h2]

theorem sum_Ico_two_mul' (m : ℕ) :
    2 * (∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), i) = 3 * m ^ 2 + m := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * m + 1 - (m + 1) = m := by omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  have h2 := Finset.sum_range_id_mul_two m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp only [Nat.succ_sub_one] at h2
    simp only [smul_eq_mul]
    nlinarith [h2]

/-- The index of an exceptional configuration. -/
noncomputable def idx (S : Finset ℕ) : ℤ := if stair S < lo S then -(#S : ℤ) else (#S : ℤ)

theorem pentSet_props {k : ℤ} (hk : k ≠ 0) :
    pentSet k ∈ parts (pentExp k) ∧ Exc (pentSet k) ∧ #(pentSet k) = k.natAbs ∧
      idx (pentSet k) = k := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hset : pentSet (-(m : ℤ)) = Finset.Ico (m + 1) (2 * m + 1) := by
      rw [pentSet, if_neg (by omega)]; simp
    obtain ⟨h0, hlo, hhi, hstair⟩ := Ico_facts (a := m + 1) (b := 2 * m + 1) (by omega) (by omega)
    rw [hset]
    have hcard : #(Finset.Ico (m + 1) (2 * m + 1)) = m := by rw [Nat.card_Ico]; omega
    have hstair' : stair (Finset.Ico (m + 1) (2 * m + 1)) = m := by rw [hstair]; omega
    have hhi' : hi (Finset.Ico (m + 1) (2 * m + 1)) = 2 * m := by rw [hhi]; omega
    have hsum : ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), i = pentExp (-(m : ℤ)) := by
      have h1 := sum_Ico_two_mul' m
      have h2 := pentExp_spec (-(m : ℤ))
      have h4 : 2 * (pentExp (-(m : ℤ)) : ℤ) = 3 * (m : ℤ) ^ 2 + m := by rw [h2]; ring
      have h3 : 2 * pentExp (-(m : ℤ)) = 3 * m ^ 2 + m := by exact_mod_cast h4
      omega
    refine ⟨mem_parts.2 ⟨h0, hsum⟩, ?_, ?_, ?_⟩
    · right; rw [hlo, hstair', hhi']; omega
    · rw [hcard]; omega
    · rw [idx, if_pos (by rw [hlo, hstair']; omega), hcard]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hset : pentSet (m : ℤ) = Finset.Ico m (2 * m) := by
      rw [pentSet, if_pos (by omega)]; simp
    obtain ⟨h0, hlo, hhi, hstair⟩ := Ico_facts (a := m) (b := 2 * m) (by omega) (by omega)
    rw [hset]
    have hcard : #(Finset.Ico m (2 * m)) = m := by rw [Nat.card_Ico]; omega
    have hstair' : stair (Finset.Ico m (2 * m)) = m := by rw [hstair]; omega
    have hhi' : hi (Finset.Ico m (2 * m)) = 2 * m - 1 := by rw [hhi]
    have hsum : ∑ i ∈ Finset.Ico m (2 * m), i = pentExp (m : ℤ) := by
      have h1 := sum_Ico_two_mul m
      have h2 := pentExp_spec (m : ℤ)
      have h4 : 2 * (pentExp (m : ℤ) : ℤ) + m = 3 * (m : ℤ) ^ 2 := by rw [h2]; ring
      have h3 : 2 * pentExp (m : ℤ) + m = 3 * m ^ 2 := by exact_mod_cast h4
      omega
    refine ⟨mem_parts.2 ⟨h0, hsum⟩, ?_, ?_, ?_⟩
    · left; rw [hlo, hstair', hhi']; omega
    · rw [hcard]; omega
    · rw [idx, if_neg (by rw [hlo, hstair']; omega), hcard]

theorem exc_eq_pentSet {n : ℕ} {S : Finset ℕ} (hn : 0 < n) (hS : S ∈ parts n) (hexc : Exc S) :
    idx S ≠ 0 ∧ pentExp (idx S) = n ∧ pentSet (idx S) = S := by
  have hne := nonempty_of_mem_parts hn hS
  obtain ⟨h0, hsum⟩ := mem_parts.1 hS
  have hsS : lo S ∈ S := lo_mem hne
  have hsM : lo S ≤ hi S := le_hi hsS
  have ht1 : 1 ≤ stair S := stair_pos h0 hne
  have htM : stair S ≤ hi S := stair_le_hi h0
  have hstair : Finset.Icc (hi S - stair S + 1) (hi S) ⊆ S := staircase_subset le_rfl
  have hMt1 : hi S - stair S + 1 ∈ S := hstair (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hsle : lo S ≤ hi S - stair S + 1 := lo_le hMt1
  rcases hexc with ⟨hst, hlt⟩ | ⟨hst, heq⟩
  · have hs1 : 1 ≤ lo S := lo_pos h0 hne
    have hkey : lo S = hi S - stair S + 1 := by omega
    have hM : hi S = 2 * lo S - 1 := by omega
    have hSeq : S = Finset.Ico (lo S) (2 * lo S) := by
      ext x
      simp only [Finset.mem_Ico]
      constructor
      · intro hx
        exact ⟨lo_le hx, by have := le_hi hx; omega⟩
      · intro hx
        exact hstair (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hcard : #S = lo S := by
      conv_lhs => rw [hSeq]
      rw [Nat.card_Ico]; omega
    have hidx : idx S = (lo S : ℤ) := by rw [idx, if_neg (by omega), hcard]
    have hk0 : idx S ≠ 0 := by rw [hidx]; omega
    have hpent : pentSet ((lo S : ℤ)) = Finset.Ico (lo S) (2 * lo S) := by
      rw [pentSet, if_pos (by omega)]; simp
    have hps : pentSet (idx S) = S := by rw [hidx, hpent]; exact hSeq.symm
    obtain ⟨hmem, -, -, -⟩ := pentSet_props hk0
    refine ⟨hk0, ?_, hps⟩
    have h9 := (mem_parts.1 hmem).2
    rw [hps, hsum] at h9
    exact h9.symm
  · have hSeq : S = Finset.Ico (stair S + 1) (2 * stair S + 1) := by
      ext x
      simp only [Finset.mem_Ico]
      constructor
      · intro hx
        have h1 := lo_le hx
        have h2 := le_hi hx
        omega
      · intro hx
        exact hstair (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hcard : #S = stair S := by
      conv_lhs => rw [hSeq]
      rw [Nat.card_Ico]; omega
    have hidx : idx S = -(stair S : ℤ) := by rw [idx, if_pos hst, hcard]
    have hk0 : idx S ≠ 0 := by rw [hidx]; omega
    have hpent : pentSet (-(stair S : ℤ)) = Finset.Ico (stair S + 1) (2 * stair S + 1) := by
      rw [pentSet, if_neg (by omega)]; simp
    have hps : pentSet (idx S) = S := by rw [hidx, hpent]; exact hSeq.symm
    obtain ⟨hmem, -, -, -⟩ := pentSet_props hk0
    refine ⟨hk0, ?_, hps⟩
    have h9 := (mem_parts.1 hmem).2
    rw [hps, hsum] at h9
    exact h9.symm

/-! ### The combinatorial pentagonal number theorem -/

theorem pentExp_zero : pentExp 0 = 0 := by decide

theorem natAbs_le_pentExp (k : ℤ) : (k.natAbs : ℤ) ≤ (pentExp k : ℤ) := by
  have h := pentExp_spec k
  have habs : (k.natAbs : ℤ) = |k| := (Int.abs_eq_natAbs k).symm
  rcases le_or_gt 0 k with hk | hk
  · rw [habs, abs_of_nonneg hk]; nlinarith
  · rw [habs, abs_of_neg hk]; nlinarith

theorem parts_zero : parts 0 = {∅} := by
  ext S
  simp only [Finset.mem_singleton, mem_parts]
  constructor
  · rintro ⟨h0, hsum⟩
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hxle : x ≤ ∑ i ∈ S, i :=
      Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    rw [hsum] at hxle
    have hx0 : x = 0 := by omega
    exact h0 (hx0 ▸ hx)
  · rintro rfl
    simp

/-- **Euler's pentagonal number theorem**, combinatorial form: the number of partitions of `n`
into an even number of distinct parts minus the number of partitions of `n` into an odd number
of distinct parts is `(-1)^k` if `n = k(3k-1)/2` for some integer `k`, and `0` otherwise. -/
theorem sum_parts_eq_pentCoeff (n : ℕ) : ∑ S ∈ parts n, (-1 : ℤ) ^ #S = pentCoeff n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [parts_zero, pentCoeff]
    simp [pentExp_zero, pentSign]
  · rw [sum_parts_eq_sum_exc hn, pentCoeff, ← Finset.sum_filter]
    refine Finset.sum_nbij' idx pentSet ?_ ?_ ?_ ?_ ?_
    · intro S hSmem
      rw [Finset.mem_filter] at hSmem
      obtain ⟨hk0, hpe, hps⟩ := exc_eq_pentSet hn hSmem.1 hSmem.2
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hle := natAbs_le_pentExp (idx S)
      rw [hpe] at hle
      exact ⟨⟨by omega, by omega⟩, hpe⟩
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pentExp_zero] at hk
        omega
      obtain ⟨hmem, hexc, -, -⟩ := pentSet_props hk0
      rw [hk.2] at hmem
      exact Finset.mem_filter.2 ⟨hmem, hexc⟩
    · intro S hSmem
      rw [Finset.mem_filter] at hSmem
      exact (exc_eq_pentSet hn hSmem.1 hSmem.2).2.2
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pentExp_zero] at hk
        omega
      exact (pentSet_props hk0).2.2.2
    · intro S hSmem
      rw [Finset.mem_filter] at hSmem
      obtain ⟨hk0, hpe, hps⟩ := exc_eq_pentSet hn hSmem.1 hSmem.2
      rw [pentSign]
      congr 1
      conv_lhs => rw [← hps]
      exact (pentSet_props hk0).2.2.1

end Franklin

