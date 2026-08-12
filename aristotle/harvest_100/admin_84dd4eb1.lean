/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/
def countBelow (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => n ∈ A)).card

/-- The upper density of a set of naturals. -/
def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (countBelow A N : ℝ) / N) atTop

/-- `A` has positive upper density: for some `δ > 0`, the counting function of `A`
exceeds `δ N` for infinitely many `N`.  This is exactly `upperDensity A > 0`
(see `hasPositiveUpperDensity_of_upperDensity_pos`). -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N ≥ M, δ * N ≤ (countBelow A N : ℝ)

/-- `A` contains an arithmetic progression of length `k` (with positive common difference). -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The finitary (Erdős–Turán) form of Szemerédi's theorem for progressions of length `k`. -/
def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset ℕ, (∀ n ∈ S, n < N) →
    δ * N ≤ (S.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

theorem hasPositiveUpperDensity_of_upperDensity_pos {A : Set ℕ}
    (h : 0 < upperDensity A) : HasPositiveUpperDensity A := by
  set f : ℕ → ℝ := fun N => (countBelow A N : ℝ) / N with hf
  have hnonneg : ∀ n, 0 ≤ f n := fun n => by positivity
  have hcb : IsCoboundedUnder (· ≤ ·) atTop f := isCoboundedUnder_le_of_le atTop hnonneg
  have hlim : limsup f atTop = upperDensity A := rfl
  refine ⟨upperDensity A / 2, by linarith, fun M => ?_⟩
  have hfreq : ∃ᶠ N in atTop, upperDensity A / 2 < f N :=
    frequently_lt_of_lt_limsup hcb (by rw [hlim]; linarith)
  obtain ⟨N, hlt, hge⟩ := (hfreq.and_eventually (eventually_ge_atTop (max M 1))).exists
  have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hge
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  refine ⟨N, le_trans (le_max_left M 1) hge, ?_⟩
  rw [hf] at hlt
  simp only at hlt
  rw [lt_div_iff₀ hNpos] at hlt
  linarith

/-- **Reduction (Lean-checked).**  The infinitary Szemerédi theorem for progressions of
length `k` -- every set of positive upper density contains a `k`-term arithmetic
progression -- follows from the finitary statement for `k`. -/
theorem furstenberg_szemeredi (k : ℕ) (hfin : FinitarySzemeredi k)
    (A : Set ℕ) (hA : HasPositiveUpperDensity A) : HasAP A k := by
  classical
  obtain ⟨δ, hδ, hδA⟩ := hA
  obtain ⟨N₀, hN₀⟩ := hfin δ hδ
  obtain ⟨N, hN, hcount⟩ := hδA N₀
  set S : Finset ℕ := (Finset.range N).filter (fun n => n ∈ A) with hS
  have hmem : ∀ n ∈ S, n < N := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1
  have hcard : δ * N ≤ (S.card : ℝ) := by
    simpa [hS, countBelow] using hcount
  obtain ⟨a, d, hd, h⟩ := hN₀ N hN S hmem hcard
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have := h i hi
  rw [hS, Finset.mem_filter] at this
  exact this.2

theorem finitarySzemeredi_zero : FinitarySzemeredi 0 := by
  intro δ _
  exact ⟨0, fun N _ S _ _ => ⟨0, 1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩

theorem finitarySzemeredi_one : FinitarySzemeredi 1 := by
  intro δ hδ
  refine ⟨1, fun N hN S _ hcard => ?_⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcard
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  refine ⟨a, 1, one_pos, fun i hi => ?_⟩
  interval_cases i
  simpa using ha

theorem finitarySzemeredi_two : FinitarySzemeredi 2 := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊, fun N hN S _ hcard => ?_⟩
  have h1 : (2:ℝ) / δ ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have h2 : (2:ℝ) ≤ δ * N := by
    rw [div_le_iff₀ hδ] at h1; linarith
  have hcard2 : (2:ℝ) ≤ (S.card : ℝ) := le_trans h2 hcard
  have hlt : 1 < S.card := by exact_mod_cast (by exact_mod_cast hcard2 : (2:ℕ) ≤ S.card)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using ha
    · have hb' : a + 1 * (b - a) = b := by omega
      rw [hb']; exact hb
  · refine ⟨b, a - b, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hb
    · have ha' : b + 1 * (a - b) = a := by omega
      rw [ha']; exact ha

/-- Longer progressions give shorter ones: the finitary statement is antitone in `k`. -/
theorem finitarySzemeredi_mono {k l : ℕ} (hkl : k ≤ l) (h : FinitarySzemeredi l) :
    FinitarySzemeredi k := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  refine ⟨N₀, fun N hN S hS hcard => ?_⟩
  obtain ⟨a, d, hd, hap⟩ := hN₀ N hN S hS hcard
  exact ⟨a, d, hd, fun i hi => hap i (lt_of_lt_of_le hi hkl)⟩

/-- Unconditional base cases: a set of positive upper density contains arithmetic
progressions of length `k` for every `k ≤ 2`. -/
theorem szemeredi_of_le_two (k : ℕ) (hk : k ≤ 2) (A : Set ℕ) (hA : HasPositiveUpperDensity A) :
    HasAP A k :=
  furstenberg_szemeredi k (finitarySzemeredi_mono hk finitarySzemeredi_two) A hA

/-- Unconditional base case: a set of positive upper density contains a two-term
arithmetic progression. -/
theorem szemeredi_two (A : Set ℕ) (hA : HasPositiveUpperDensity A) : HasAP A 2 :=
  furstenberg_szemeredi 2 finitarySzemeredi_two A hA

/-- The same reduction, stated for sets whose upper density (a `limsup`) is positive. -/
theorem furstenberg_szemeredi_of_upperDensity_pos (k : ℕ) (hfin : FinitarySzemeredi k)
    (A : Set ℕ) (hA : 0 < upperDensity A) : HasAP A k :=
  furstenberg_szemeredi k hfin A (hasPositiveUpperDensity_of_upperDensity_pos hA)

/-- The multiple-recurrence formulation is equivalent to the existence of progressions. -/
theorem multiple_recurrence_iff_hasAP (A : Set ℕ) (k : ℕ) :
    (∃ d : ℕ, 0 < d ∧ (⋂ i ∈ Finset.range k, (fun n => n + i * d) ⁻¹' A).Nonempty) ↔
      HasAP A k := by
  constructor
  · rintro ⟨d, hd, a, ha⟩
    refine ⟨a, d, hd, fun i hi => ?_⟩
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_preimage] at ha
    exact ha i hi
  · rintro ⟨a, d, hd, h⟩
    refine ⟨d, hd, a, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_preimage]
    exact fun i hi => h i hi

end

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

