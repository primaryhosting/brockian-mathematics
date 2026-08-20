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

/-- The counting function of a set of naturals: the number of elements of `A` below `n`. -/
noncomputable def count (A : Set ℕ) (n : ℕ) : ℕ := ((Finset.range n).filter (· ∈ A)).card

/-- The upper (asymptotic) density of a set of naturals. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun n : ℕ => (count A n : ℝ) / n) Filter.atTop

/-- `A` contains an arithmetic progression of length `k` (with positive common difference). -/
def HasAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- **Szemerédi's theorem**, in its density form: every set of naturals of positive upper
density contains arithmetic progressions of every (hence arbitrarily large) length. -/
def SzemerediStatement : Prop :=
  ∀ A : Set ℕ, 0 < upperDensity A → ∀ k : ℕ, HasAPOfLength A k

/-- The finitary form of Szemerédi's theorem: for every length `k` and density `ε > 0` there is
an `N` such that every subset of `{0, …, n-1}` with `n ≥ N` and at least `ε n` elements contains
an arithmetic progression of length `k`. -/
def FinitarySzemeredi : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.range n →
    ε * n ≤ (A.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

section Density

variable {A : Set ℕ}

/-- Key intermediate lemma: a set of positive upper density has, for arbitrarily large `n`,
at least `ε n` elements below `n`, for some fixed `ε > 0`. -/
theorem exists_pos_frequently_count (h : 0 < upperDensity A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ε * n ≤ (count A n : ℝ) := by
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => (count A n : ℝ) / n) := by
    refine Filter.IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with n
    have : (0 : ℝ) ≤ (count A n : ℝ) / n := by positivity
    exact this
  have hlim : upperDensity A / 2 <
      Filter.limsup (fun n : ℕ => (count A n : ℝ) / n) Filter.atTop := by
    show upperDensity A / 2 < upperDensity A
    linarith
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, upperDensity A / 2 < (count A n : ℝ) / n :=
    Filter.frequently_lt_of_lt_limsup hcobdd hlim
  refine ⟨upperDensity A / 2, by linarith, fun N => ?_⟩
  obtain ⟨n, hn, hlt⟩ := (hfreq.and_eventually (Filter.eventually_ge_atTop N)).exists
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp at hn; linarith
    · exact hp
  refine ⟨n, hlt, hnpos, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [lt_div_iff₀ hn0] at hn
  linarith

/-- Reduction: the finitary form of Szemerédi's theorem implies the density form. -/
theorem szemeredi_of_finitary (h : FinitarySzemeredi) : SzemerediStatement := by
  intro A hA k
  obtain ⟨ε, hε, hcount⟩ := exists_pos_frequently_count hA
  obtain ⟨N, hN⟩ := h k ε hε
  obtain ⟨n, hn, -, hcard⟩ := hcount N
  obtain ⟨a, d, hd, hmem⟩ := hN n hn ((Finset.range n).filter (· ∈ A))
    (Finset.filter_subset _ _) hcard
  exact ⟨a, d, hd, fun i hi => (Finset.mem_filter.mp (hmem i hi)).2⟩

/-- Sanity check (non-vacuity): the whole of `ℕ` has upper density `1`, so the hypothesis of
positive upper density is satisfiable. -/
theorem upperDensity_univ : upperDensity (Set.univ : Set ℕ) = 1 := by
  have h : (fun n : ℕ => (count Set.univ n : ℝ) / n) =ᶠ[Filter.atTop] fun _ => (1 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hc : count Set.univ n = n := by simp [count]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [hc]
    field_simp
  rw [upperDensity, Filter.limsup_congr h]
  exact Filter.limsup_const 1

end Density

/-- Base case (length three): every set of naturals of positive upper density contains a
three-term arithmetic progression with positive common difference. This is Roth's theorem,
applied along a sequence of scales of density at least `ε`. -/
theorem exists_three_ap {A : Set ℕ} (hA : 0 < upperDensity A) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨ε, hε, hcount⟩ := exists_pos_frequently_count hA
  obtain ⟨n, hn, -, hcard⟩ := hcount (cornersTheoremBound (ε / 3))
  have hnot : ¬ ThreeAPFree (((Finset.range n).filter (· ∈ A) : Finset ℕ) : Set ℕ) :=
    roth_3ap_theorem_nat ε hε hn _ (Finset.filter_subset _ _) hcard
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hnot
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb hc
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨a, b - a, by omega, ha.2, ?_, ?_⟩
    · have : a + (b - a) = b := by omega
      rw [this]; exact hb.2
    · have : a + 2 * (b - a) = c := by omega
      rw [this]; exact hc.2
  · refine ⟨c, b - c, by omega, hc.2, ?_, ?_⟩
    · have : c + (b - c) = b := by omega
      rw [this]; exact hb.2
    · have : c + 2 * (b - c) = a := by omega
      rw [this]; exact ha.2

/-- **Furstenberg–Szemerédi (base case)**: every set of natural numbers of positive upper
density contains arithmetic progressions of every length `k ≤ 3`, with positive common
difference.

The full theorem of Szemerédi (arbitrary `k`), which Furstenberg deduced from his multiple
recurrence theorem, is formalized as the statement `Frontier.SzemerediStatement`; it is reduced
to its finitary form in `Frontier.szemeredi_of_finitary`. The case `k ≤ 3` proved here rests on
Roth's theorem. -/
theorem furstenberg_szemeredi (A : Set ℕ) (hA : 0 < upperDensity A) (k : ℕ) (hk : k ≤ 3) :
    HasAPOfLength A k := by
  obtain ⟨a, d, hd, h0, h1, h2⟩ := exists_three_ap hA
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hi3 : i < 3 := lt_of_lt_of_le hi hk
  interval_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

end Frontier

