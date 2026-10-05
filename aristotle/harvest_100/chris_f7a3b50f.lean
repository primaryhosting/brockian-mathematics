/-
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

/-- `countUpTo A N` is the number of elements of `A` below `N`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => n ∈ A)).card

/-- The upper (Banach) density of a set of naturals, `limsup_N |A ∩ [0,N)| / N`. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countUpTo A N : ℝ) / N) Filter.atTop

/-- `HasAP A k` says that `A` contains an arithmetic progression of length `k`
(with positive common difference). -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The finitary form of Szemerédi's theorem: for every length `k` and every density
`δ > 0` there is `N₀` such that any subset of `{0, …, N-1}` with `N ≥ N₀` of size at
least `δ N` contains a `k`-term arithmetic progression.  This is exactly the statement
that Furstenberg's multiple recurrence theorem yields via the correspondence principle. -/
def SzemerediFinitary : Prop :=
  ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset ℕ, S ⊆ Finset.range N →
    δ * (N : ℝ) ≤ (S.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- A set of positive upper density has, for some fixed `δ > 0`, arbitrarily large
counting windows in which its density is at least `δ`. -/
theorem exists_density_windows (A : Set ℕ) (h : 0 < upperDensity A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ δ * (N : ℝ) ≤ (countUpTo A N : ℝ) := by
  set f : ℕ → ℝ := fun N => (countUpTo A N : ℝ) / N with hf
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop f :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop hnn
  set c : ℝ := upperDensity A with hc
  have hfreq : ∃ᶠ N in Filter.atTop, c / 2 < f N := by
    apply Filter.frequently_lt_of_lt_limsup hcob
    have : Filter.limsup f Filter.atTop = c := rfl
    rw [this]
    linarith
  refine ⟨c / 2, by linarith, ?_⟩
  intro M
  obtain ⟨N, hlt, hN⟩ := (hfreq.and_eventually (Filter.eventually_ge_atTop (max M 1))).exists
  refine ⟨N, le_trans (le_max_left _ _) hN, ?_⟩
  have hN1 : (1 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have h2 : c / 2 * (N : ℝ) < (countUpTo A N : ℝ) :=
    (lt_div_iff₀ hNpos).mp (by simpa [hf] using hlt)
  linarith

/-- A set of positive upper density is infinite. -/
theorem infinite_of_upperDensity_pos (A : Set ℕ) (h : 0 < upperDensity A) : A.Infinite := by
  obtain ⟨δ, hδ, hwin⟩ := exists_density_windows A h
  by_contra hfin
  rw [Set.not_infinite] at hfin
  set c : ℕ := hfin.toFinset.card with hcdef
  have hbound : ∀ N : ℕ, countUpTo A N ≤ c := by
    intro N
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact hfin.mem_toFinset.mpr hx.2
  obtain ⟨M, hM⟩ := exists_nat_gt (((c : ℝ) + 1) / δ)
  obtain ⟨N, hNM, hN⟩ := hwin M
  have hMN : ((c : ℝ) + 1) / δ < (N : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hNM)
  have h1 : (c : ℝ) + 1 < δ * N := by
    rw [div_lt_iff₀ hδ] at hMN; linarith
  have h2 : (countUpTo A N : ℝ) ≤ (c : ℝ) := by exact_mod_cast hbound N
  linarith

/-- The finitary Szemerédi statement is unconditionally true for progression lengths
`k ≤ 2`: a subset of `{0, …, N-1}` of size at least `δ N` with `N` large has two distinct
elements, hence a two-term progression. -/
theorem szemerediFinitary_of_le_two (k : ℕ) (hk : k ≤ 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset ℕ, S ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (S.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / δ)
  refine ⟨N₀, ?_⟩
  intro N hN S _ hcard
  have hNle : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (2 : ℝ) < δ * (N : ℝ) := by
    rw [div_lt_iff₀ hδ] at hN₀
    nlinarith
  have hc : 1 < S.card := by
    have : (1 : ℝ) < (S.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · refine ⟨x, y - x, by omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi hk
    interval_cases i
    · simpa using hx
    · have : x + 1 * (y - x) = y := by omega
      rw [this]; exact hy
  · refine ⟨y, x - y, by omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi hk
    interval_cases i
    · simpa using hy
    · have : y + 1 * (x - y) = x := by omega
      rw [this]; exact hx

/-- **Furstenberg–Szemerédi.**

The first component is the unconditional base case: a set of naturals of positive upper
density contains arithmetic progressions of length `k ≤ 2`.

The second component is a Lean-checked reduction: the finitary Szemerédi statement
`SzemerediFinitary` — which is what Furstenberg's multiple recurrence theorem produces
through the Furstenberg correspondence principle — implies the density statement that
every subset of `ℕ` of positive upper density contains arbitrarily long arithmetic
progressions. -/
theorem furstenberg_szemeredi :
    (∀ A : Set ℕ, 0 < upperDensity A → ∀ k ≤ 2, HasAP A k) ∧
    (SzemerediFinitary → ∀ A : Set ℕ, 0 < upperDensity A → ∀ k : ℕ, HasAP A k) := by
  constructor
  · -- base case `k ≤ 2`
    intro A hA k hk
    have hinf := infinite_of_upperDensity_pos A hA
    obtain ⟨a, ha⟩ := hinf.nonempty
    have : ((A \ {n : ℕ | n ≤ a}) : Set ℕ).Nonempty := by
      have : ((A \ {n : ℕ | n ≤ a}) : Set ℕ).Infinite :=
        hinf.diff (Set.Finite.subset (Set.finite_Iic a) (by intro x hx; exact hx))
      exact this.nonempty
    obtain ⟨b, hb, hba⟩ := this
    simp only [Set.mem_setOf_eq, not_le] at hba
    refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi hk
    interval_cases i
    · simpa using ha
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hb
  · -- reduction from the finitary statement
    intro hSz A hA k
    obtain ⟨δ, hδ, hwin⟩ := exists_density_windows A hA
    obtain ⟨N₀, hN₀⟩ := hSz k δ hδ
    obtain ⟨N, hNM, hN⟩ := hwin N₀
    obtain ⟨a, d, hd, hmem⟩ :=
      hN₀ N hNM ((Finset.range N).filter (fun n => n ∈ A)) (Finset.filter_subset _ _)
        (by simpa [countUpTo] using hN)
    exact ⟨a, d, hd, fun i hi => (Finset.mem_filter.mp (hmem i hi)).2⟩

end Frontier

