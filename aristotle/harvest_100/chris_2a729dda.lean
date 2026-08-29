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

/-- The number of elements of `A` below `n`. -/
noncomputable def countIn (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun x => x ∈ A)).card

/-- `A ⊆ ℕ` has positive upper density: there is `δ > 0` such that the counting function
`countIn A n` is at least `δ * n` for infinitely many `n`. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ δ * n ≤ (countIn A n : ℝ)

/-- `A` contains an arithmetic progression of length `k` with positive common difference. -/
def HasAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- Szemerédi's theorem for progressions of length `k`, as a statement. -/
def SzemerediStatement (k : ℕ) : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A → HasAPOfLength A k

/-- A set of positive upper density is unbounded. -/
lemma exists_mem_gt {A : Set ℕ} (hA : HasPositiveUpperDensity A) (m : ℕ) :
    ∃ x ∈ A, m < x := by
  obtain ⟨δ, hδ, h⟩ := hA
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, hn, hcard⟩ := h ⌈((m : ℝ) + 2) / δ⌉₊
  have h1 : countIn A n ≤ m + 1 := by
    have hsub : (Finset.range n).filter (fun x => x ∈ A) ⊆ Finset.range (m + 1) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (hcon x hx.2)
    simpa [countIn] using Finset.card_le_card hsub
  have hn' : ((m : ℝ) + 2) / δ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : ((m : ℝ) + 2) ≤ δ * n := by rw [← div_le_iff₀' hδ]; exact hn'
  have h3 : (countIn A n : ℝ) ≤ (m : ℝ) + 1 := by
    have : (countIn A n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  linarith

/-- Roth's theorem in `ℕ`: a set of positive upper density contains a nontrivial
three-term arithmetic progression. -/
lemma exists_three_ap {A : Set ℕ} (hA : HasPositiveUpperDensity A) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨δ, hδ, h⟩ := hA
  obtain ⟨n, hn, hcard⟩ := h (cornersTheoremBound (δ / 3))
  have hnot := roth_3ap_theorem_nat δ hδ hn ((Finset.range n).filter (fun x => x ∈ A))
    (Finset.filter_subset _ _) (by simpa [countIn] using hcard)
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hnot
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb hc
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨a, b - a, by omega, ha.2, ?_, ?_⟩
    · have e : a + (b - a) = b := by omega
      rw [e]; exact hb.2
    · have e : a + 2 * (b - a) = c := by omega
      rw [e]; exact hc.2
  · refine ⟨c, b - c, by omega, hc.2, ?_, ?_⟩
    · have e : c + (b - c) = b := by omega
      rw [e]; exact hb.2
    · have e : c + 2 * (b - c) = a := by omega
      rw [e]; exact ha.2

/-- **Furstenberg–Szemerédi (case `k ≤ 3`).**
Every set of natural numbers of positive upper density contains an arithmetic progression of
length `k` for every `k ≤ 3`.  The cases `k ≤ 2` are elementary; the case `k = 3` is Roth's
theorem. -/
theorem furstenberg_szemeredi {A : Set ℕ} (hA : HasPositiveUpperDensity A) {k : ℕ}
    (hk : k ≤ 3) : HasAPOfLength A k := by
  interval_cases k
  · exact ⟨0, 1, one_pos, fun i hi => absurd hi (by omega)⟩
  · obtain ⟨x, hx, -⟩ := exists_mem_gt hA 0
    refine ⟨x, 1, one_pos, fun i hi => ?_⟩
    interval_cases i
    simpa using hx
  · obtain ⟨x, hx, -⟩ := exists_mem_gt hA 0
    obtain ⟨y, hy, hxy⟩ := exists_mem_gt hA x
    refine ⟨x, y - x, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hx
    · have e : x + 1 * (y - x) = y := by omega
      rw [e]; exact hy
  · obtain ⟨a, d, hd, h0, h1, h2⟩ := exists_three_ap hA
    refine ⟨a, d, hd, fun i hi => ?_⟩
    interval_cases i
    · simpa using h0
    · simpa using h1
    · exact h2

/-- The finitary (density) form of Szemerédi's theorem for progressions of length `k`:
for every `δ > 0` all sufficiently long initial segments of `ℕ` have the property that any
subset of density at least `δ` contains a `k`-term arithmetic progression. -/
def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ B : Finset ℕ, B ⊆ Finset.range n →
    δ * n ≤ (B.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B

/-- **Lean-checked reduction.** The infinitary Szemerédi statement for progressions of length
`k` follows from its finitary density form. -/
theorem szemerediStatement_of_finitary {k : ℕ} (h : FinitarySzemeredi k) :
    SzemerediStatement k := by
  rintro A ⟨δ, hδ, hden⟩
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  obtain ⟨n, hn, hcard⟩ := hden N₀
  obtain ⟨a, d, hd, hmem⟩ :=
    hN₀ n hn ((Finset.range n).filter (fun x => x ∈ A)) (Finset.filter_subset _ _)
      (by simpa [countIn] using hcard)
  exact ⟨a, d, hd, fun i hi => (Finset.mem_filter.1 (hmem i hi)).2⟩

/-- The statement of Szemerédi's theorem holds for all lengths `k ≤ 3`. -/
theorem szemerediStatement_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediStatement k :=
  fun _ hA => furstenberg_szemeredi hA hk

end Frontier

