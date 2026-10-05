/-
Companion file to `RequestProject.FurstenbergSzemeredi`.

Here we prove the *converse* reduction: if every subset of `ℕ` of positive upper density
contains arithmetic progressions of length `k`, then the finitary Szemerédi property
`SzemerediFinitaryAt k` holds.  Consequently the hypothesis used in
`Frontier.furstenberg_szemeredi` is exactly equivalent to its conclusion, so the reduction
is lossless.

The proof is by contraposition: from a family of progression-free subsets of `[0, M)` of
density `≥ δ` with `M` arbitrarily large, we build a single set of positive upper density
with no progression of length `k`, by placing the `j`-th example in the interval
`[2 Lⱼ, 3 Lⱼ)` with the lengths `Lⱼ` growing at least geometrically with ratio `300`.
-/

import Mathlib
import RequestProject.FurstenbergSzemeredi

namespace Frontier

open scoped Classical

section Converse

variable (Mf : ℕ → ℕ) (Sf : ℕ → Finset ℕ)

/-- The thresholds used to select the successive blocks. -/
def blockArg : ℕ → ℕ
  | 0 => 1
  | j + 1 => 300 * Mf (blockArg j) + 1

/-- The length of the `j`-th block. -/
def blockLen (j : ℕ) : ℕ := Mf (blockArg Mf j)

/-- The `j`-th block: the selected progression-free set translated into
`[2 * blockLen j, 3 * blockLen j)`. -/
def blockSet (j : ℕ) : Finset ℕ :=
  (Sf (blockArg Mf j)).image (fun s => 2 * blockLen Mf j + s)

/-- The set built out of all the blocks. -/
def blockUnion : Set ℕ := ⋃ j, (blockSet Mf Sf j : Set ℕ)

variable {Mf}

/-- Each selected length is at least its threshold. -/
theorem blockArg_le_blockLen (hM : ∀ N, N ≤ Mf N) (j : ℕ) : blockArg Mf j ≤ blockLen Mf j :=
  hM _

theorem blockLen_pos (hM : ∀ N, N ≤ Mf N) (j : ℕ) : 0 < blockLen Mf j := by
  have := blockArg_le_blockLen hM j
  have h : 0 < blockArg Mf j := by
    cases j with
    | zero => simp [blockArg]
    | succ j => simp [blockArg]
  omega

theorem blockLen_succ (hM : ∀ N, N ≤ Mf N) (j : ℕ) :
    300 * blockLen Mf j + 1 ≤ blockLen Mf (j + 1) := by
  have h := blockArg_le_blockLen hM (j + 1)
  simpa [blockArg, blockLen] using h

/-- The block lengths grow at least by the factor `300` at each step. -/
theorem blockLen_growth (hM : ∀ N, N ≤ Mf N) {i j : ℕ} (hij : i < j) :
    300 * blockLen Mf i < blockLen Mf j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · have h1 := ih h
      have h2 := blockLen_succ hM j
      have h3 : 0 ≤ blockLen Mf j := Nat.zero_le _
      omega
    · subst h
      have := blockLen_succ hM i
      omega

theorem self_le_blockLen (hM : ∀ N, N ≤ Mf N) (j : ℕ) : j ≤ blockLen Mf j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have := blockLen_succ hM j
    omega

variable {Sf}

/-- Membership in a block, unfolded. -/
theorem mem_blockSet_iff (j x : ℕ) :
    x ∈ blockSet Mf Sf j ↔ ∃ s ∈ Sf (blockArg Mf j), x = 2 * blockLen Mf j + s := by
  simp only [blockSet, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

/-- Elements of the `j`-th block lie in `[2 Lⱼ, 3 Lⱼ)`. -/
theorem blockSet_bounds (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N)) {j x : ℕ}
    (hx : x ∈ blockSet Mf Sf j) :
    2 * blockLen Mf j ≤ x ∧ x < 3 * blockLen Mf j := by
  rw [mem_blockSet_iff] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have : s < Mf (blockArg Mf j) := Finset.mem_range.mp (hSub _ hs)
  simp only [blockLen]
  omega

theorem mem_blockUnion_iff (x : ℕ) :
    x ∈ blockUnion Mf Sf ↔ ∃ j, x ∈ blockSet Mf Sf j := by
  simp [blockUnion]

/-- The block containing an element is determined by the position of that element. -/
theorem blockSet_of_mem_blockUnion (hM : ∀ N, N ≤ Mf N)
    (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N)) {x j : ℕ} (hx : x ∈ blockUnion Mf Sf)
    (h1 : 2 * blockLen Mf j ≤ x) (h2 : x < 3 * blockLen Mf j) : x ∈ blockSet Mf Sf j := by
  rw [mem_blockUnion_iff] at hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨hi1, hi2⟩ := blockSet_bounds hSub hi
  rcases lt_trichotomy i j with h | h | h
  · exfalso
    have := blockLen_growth hM h
    omega
  · subst h; exact hi
  · exfalso
    have := blockLen_growth hM h
    omega

/-- Below the `j`-th block, all elements of the constructed set are very small. -/
theorem small_of_lt_block (hM : ∀ N, N ≤ Mf N) (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N))
    {x j : ℕ} (hx : x ∈ blockUnion Mf Sf) (hlt : x < 2 * blockLen Mf j) :
    100 * x < blockLen Mf j := by
  rw [mem_blockUnion_iff] at hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨hi1, hi2⟩ := blockSet_bounds hSub hi
  have hij : i < j := by
    by_contra hc
    push_neg at hc
    rcases eq_or_lt_of_le hc with h | h
    · subst h; omega
    · have := blockLen_growth hM h
      omega
  have := blockLen_growth hM hij
  omega

/-- The constructed set has positive upper density. -/
theorem hasPosUpperDensity_blockUnion {δ : ℝ} (hδ : 0 < δ) (hM : ∀ N, N ≤ Mf N)
    (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N))
    (hCard : ∀ N, δ * (Mf N : ℝ) ≤ ((Sf N).card : ℝ)) :
    HasPosUpperDensity (blockUnion Mf Sf) := by
  refine ⟨δ / 3, by positivity, fun N => ?_⟩
  refine ⟨3 * blockLen Mf N, ?_, ?_⟩
  · have := self_le_blockLen hM N
    omega
  · have hcard_image : (blockSet Mf Sf N).card = (Sf (blockArg Mf N)).card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      simpa using hxy
    have hsub : blockSet Mf Sf N ⊆
        (Finset.range (3 * blockLen Mf N)).filter (fun n => n ∈ blockUnion Mf Sf) := by
      intro x hx
      have hb := blockSet_bounds hSub hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb.2, ?_⟩
      exact (mem_blockUnion_iff x).mpr ⟨N, hx⟩
    have h1 : ((blockSet Mf Sf N).card : ℝ) ≤
        ((((Finset.range (3 * blockLen Mf N)).filter
          (fun n => n ∈ blockUnion Mf Sf)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : δ * (blockLen Mf N : ℝ) ≤ ((blockSet Mf Sf N).card : ℝ) := by
      rw [hcard_image]
      exact hCard (blockArg Mf N)
    have h3 : δ / 3 * ((3 * blockLen Mf N : ℕ) : ℝ) = δ * (blockLen Mf N : ℝ) := by
      push_cast; ring
    rw [h3]
    linarith

/-- The constructed set contains no arithmetic progression of length `k` (for `k ≥ 3`). -/
theorem not_hasAP_blockUnion {k : ℕ} (hk : 3 ≤ k) (hM : ∀ N, N ≤ Mf N)
    (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N))
    (hNo : ∀ N, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Sf N) :
    ¬ HasAP (blockUnion Mf Sf) k := by
  rintro ⟨a, d, hd, hAP⟩
  -- the largest term of the progression determines a block `j`
  have htop : a + (k - 1) * d ∈ blockUnion Mf Sf := hAP (k - 1) (by omega)
  obtain ⟨j, hj⟩ := (mem_blockUnion_iff _).mp htop
  obtain ⟨hb1, hb2⟩ := blockSet_bounds hSub hj
  have hLpos : 0 < blockLen Mf j := blockLen_pos hM j
  have hmono : ∀ i, i < k → a + i * d ≤ a + (k - 1) * d := by
    intro i hi
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  by_cases hcase : 2 * blockLen Mf j ≤ a
  · -- every term lies in the block `j`, contradicting progression-freeness of the block
    refine hNo (blockArg Mf j) ⟨a - 2 * blockLen Mf j, d, hd, fun i hi => ?_⟩
    have hmem : a + i * d ∈ blockUnion Mf Sf := hAP i hi
    have hle := hmono i hi
    have hin : a + i * d ∈ blockSet Mf Sf j :=
      blockSet_of_mem_blockUnion hM hSub hmem (by omega) (by omega)
    obtain ⟨s, hs, hseq⟩ := (mem_blockSet_iff _ _).mp hin
    have hrw : a - 2 * blockLen Mf j + i * d = s := by omega
    rw [hrw]; exact hs
  · -- otherwise the progression jumps over the (long) gap preceding the block `j`
    push_neg at hcase
    have hex : ∃ i, 2 * blockLen Mf j ≤ a + i * d := ⟨k - 1, hb1⟩
    have hmspec : 2 * blockLen Mf j ≤ a + Nat.find hex * d := Nat.find_spec hex
    have hm0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h] at hmspec
      simp at hmspec
      omega
    have hmin : ¬ (2 * blockLen Mf j ≤ a + (Nat.find hex - 1) * d) :=
      Nat.find_min hex (by omega)
    push_neg at hmin
    have hmk : Nat.find hex ≤ k - 1 := Nat.find_le hb1
    have hprev : a + (Nat.find hex - 1) * d ∈ blockUnion Mf Sf := hAP _ (by omega)
    have hsmall : 100 * (a + (Nat.find hex - 1) * d) < blockLen Mf j :=
      small_of_lt_block hM hSub hprev hmin
    have hstep : a + Nat.find hex * d = (a + (Nat.find hex - 1) * d) + d := by
      have hm1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      calc a + Nat.find hex * d = a + (Nat.find hex - 1 + 1) * d := by rw [hm1]
        _ = (a + (Nat.find hex - 1) * d) + d := by ring
    have hspan : (k - 1) * d ≤ 3 * blockLen Mf j := le_of_lt (by omega)
    have h2d : 2 * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega

end Converse

/-- **Converse reduction.** If every set of positive upper density contains an arithmetic
progression of length `k`, then the finitary Szemerédi property holds at `k`. -/
theorem szemerediFinitaryAt_of_forall_hasAP (k : ℕ)
    (h : ∀ A : Set ℕ, HasPosUpperDensity A → HasAP A k) : SzemerediFinitaryAt k := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · exact szemerediFinitaryAt_of_le_two (by omega)
  by_contra hcon
  unfold SzemerediFinitaryAt at hcon
  push_neg at hcon
  obtain ⟨δ, hδ, hbad⟩ := hcon
  -- extract, for every threshold `N`, a progression-free dense subset of some `[0, M)`
  have hbad' : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧
      δ * (M : ℝ) ≤ (S.card : ℝ) ∧ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
    intro N
    obtain ⟨M, hNM, S, hS, hcard, hno⟩ := hbad N
    exact ⟨M, hNM, S, hS, hcard, by
      rintro ⟨a, d, hd, hAP⟩
      obtain ⟨i, hi, hi'⟩ := hno a d hd
      exact hi' (hAP i hi)⟩
  choose Mf hM Sf hSub hCard hNo using hbad'
  have hpos := hasPosUpperDensity_blockUnion hδ hM hSub hCard
  exact not_hasAP_blockUnion (by omega) hM hSub hNo (h _ hpos)

/-- **Equivalence.** The finitary Szemerédi property is equivalent to the statement that
every subset of `ℕ` of positive upper density contains arbitrarily long arithmetic
progressions.  In particular the hypothesis of `Frontier.furstenberg_szemeredi` is not
stronger than its conclusion. -/
theorem szemerediFinitary_iff_forall_hasAP :
    SzemerediFinitary ↔ ∀ A : Set ℕ, HasPosUpperDensity A → ∀ k, HasAP A k := by
  constructor
  · intro hSz A hA k; exact furstenberg_szemeredi hSz hA k
  · intro h k
    exact szemerediFinitaryAt_of_forall_hasAP k (fun A hA => h A hA k)

end Frontier

/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the header
-- above is a plain comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Frontier

/-- `HasAP A k` says that the set `A ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with positive common difference `d`. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `HasPosUpperDensity A` says that the upper density of `A ⊆ ℕ` along the initial
intervals `[0, M)` is positive: there is `δ > 0` with `|A ∩ [0, M)| ≥ δ M` for
arbitrarily large `M`. -/
def HasPosUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    δ * M ≤ (((Finset.range M).filter (fun n => n ∈ A)).card : ℝ)

/-- The finitary Szemerédi property for progressions of a fixed length `k`
(the combinatorial content of Furstenberg's multiple recurrence theorem at level `k`):
for every density `δ > 0` there is a threshold `N` such that every subset of `[0, M)`
with `M ≥ N` and of size at least `δ M` contains an arithmetic progression of length `k`. -/
def SzemerediFinitaryAt (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ∀ S : Finset ℕ,
    S ⊆ Finset.range M → δ * M ≤ (S.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- The finitary form of Szemerédi's theorem: `SzemerediFinitaryAt k` for every `k`. -/
def SzemerediFinitary : Prop := ∀ k : ℕ, SzemerediFinitaryAt k

/-- Progressions of length `k` are also progressions of any shorter length, so the
finitary Szemerédi property is monotone (downwards) in the length. -/
theorem SzemerediFinitaryAt.mono {k l : ℕ} (hkl : k ≤ l) (h : SzemerediFinitaryAt l) :
    SzemerediFinitaryAt k := by
  intro δ hδ
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun M hM S hS hcard => ?_⟩
  obtain ⟨a, d, hd, hAP⟩ := hN M hM S hS hcard
  exact ⟨a, d, hd, fun i hi => hAP i (lt_of_lt_of_le hi hkl)⟩

/-- **Base case, `k = 2`.** The finitary Szemerédi property holds unconditionally for
progressions of length `2`: a subset of `[0, M)` of size at least `δ M ≥ 2` has two
distinct elements. -/
theorem szemerediFinitaryAt_two : SzemerediFinitaryAt 2 := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊, fun M hM S _ hcard => ?_⟩
  -- from `M ≥ ⌈2/δ⌉` we get `δ * M ≥ 2`, hence `S` has at least two elements
  have hMR : 2 / δ ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hM)
  have h2 : (2 : ℝ) ≤ δ * M := by
    rw [div_le_iff₀ hδ] at hMR; linarith
  have hcard2 : 2 ≤ S.card := by exact_mod_cast le_trans h2 hcard
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using ha
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hb
  · refine ⟨b, a - b, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hb
    · have : b + 1 * (a - b) = a := by omega
      rw [this]; exact ha

/-- The finitary Szemerédi property for lengths `0` and `1` follows from the base case. -/
theorem szemerediFinitaryAt_of_le_two {k : ℕ} (hk : k ≤ 2) : SzemerediFinitaryAt k :=
  szemerediFinitaryAt_two.mono hk

/-- **The reduction, at a fixed length.** If the finitary Szemerédi property holds for
length `k`, then every set of positive upper density contains an arithmetic progression
of length `k`. -/
theorem hasAP_of_szemerediFinitaryAt {k : ℕ} (hSz : SzemerediFinitaryAt k) {A : Set ℕ}
    (hA : HasPosUpperDensity A) : HasAP A k := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N, hN⟩ := hSz δ hδ
  obtain ⟨M, hNM, hM⟩ := hdens N
  obtain ⟨a, d, hd, hAP⟩ := hN M hNM ((Finset.range M).filter (fun n => n ∈ A))
    (Finset.filter_subset _ _) hM
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hmem := hAP i hi
  simp only [Finset.mem_filter] at hmem
  exact hmem.2

/-- **Furstenberg–Szemerédi.** Assuming the finitary Szemerédi property (equivalently, the
combinatorial content of Furstenberg's multiple recurrence theorem), every subset of `ℕ`
of positive upper density contains arithmetic progressions of every length. -/
theorem furstenberg_szemeredi (hSz : SzemerediFinitary) {A : Set ℕ}
    (hA : HasPosUpperDensity A) (k : ℕ) : HasAP A k :=
  hasAP_of_szemerediFinitaryAt (hSz k) hA

/-- A set of positive upper density is infinite. -/
theorem infinite_of_hasPosUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) : A.Infinite := by
  obtain ⟨δ, hδ, h⟩ := hA
  by_contra hc
  rw [Set.not_infinite] at hc
  obtain ⟨N, hN⟩ := exists_nat_gt ((hc.toFinset.card : ℝ) / δ)
  obtain ⟨M, hNM, hM⟩ := h N
  have hsub : ((Finset.range M).filter (fun n => n ∈ A)) ⊆ hc.toFinset := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simpa using hx.2
  have hcard : ((((Finset.range M).filter (fun n => n ∈ A)).card : ℝ)) ≤ hc.toFinset.card := by
    exact_mod_cast Finset.card_le_card hsub
  have h1 : (hc.toFinset.card : ℝ) < δ * N := by
    rw [div_lt_iff₀ hδ] at hN; linarith
  have h2 : δ * (N : ℝ) ≤ δ * M := by
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    nlinarith
  linarith

/-- **Unconditional base case of Furstenberg–Szemerédi.** A set of positive upper density
contains a two-term arithmetic progression. -/
theorem hasAP_two_of_hasPosUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) : HasAP A 2 :=
  hasAP_of_szemerediFinitaryAt szemerediFinitaryAt_two hA

/-- Sanity check: the hypothesis `HasPosUpperDensity` is satisfiable (`ℕ` itself has
upper density `1`). -/
theorem hasPosUpperDensity_univ : HasPosUpperDensity (Set.univ : Set ℕ) := by
  refine ⟨1, one_pos, fun N => ⟨N, le_rfl, ?_⟩⟩
  simp

/-- **Unconditional case `k ≤ 2` of Furstenberg–Szemerédi.** -/
theorem hasAP_of_hasPosUpperDensity_of_le_two {A : Set ℕ} (hA : HasPosUpperDensity A)
    {k : ℕ} (hk : k ≤ 2) : HasAP A k :=
  hasAP_of_szemerediFinitaryAt (szemerediFinitaryAt_of_le_two hk) hA

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

