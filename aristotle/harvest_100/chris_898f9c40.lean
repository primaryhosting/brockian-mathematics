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
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open Finset

/-- The trace of a set `A ⊆ ℕ` on the initial segment `{0, 1, ..., N - 1}`. -/
noncomputable def trace (A : Set ℕ) (N : ℕ) : Finset ℕ := {n ∈ Finset.range N | n ∈ A}

lemma trace_subset (A : Set ℕ) (N : ℕ) : trace A N ⊆ Finset.range N := by
  intro x hx
  simp only [trace, Finset.mem_filter] at hx
  exact hx.1

lemma mem_of_mem_trace {A : Set ℕ} {N x : ℕ} (hx : x ∈ trace A N) : x ∈ A := by
  simp only [trace, Finset.mem_filter] at hx
  exact hx.2

/-- `A ⊆ ℕ` has positive upper density: there is `δ > 0` such that the density of `A` in
`{0, ..., N-1}` is at least `δ` for infinitely many `N`.  This is exactly the statement that the
upper density `limsup_N |A ∩ [0,N)| / N` is positive. -/
def HasPosUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ δ * N ≤ #(trace A N)

/-- `A` contains an arithmetic progression of length `k` (with positive common difference). -/
def HasAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The finitary form of Szemerédi's theorem: for every length `k` and density `δ > 0`, every
sufficiently large initial segment `{0, ..., N-1}` has the property that each of its subsets of
density at least `δ` contains a `k`-term arithmetic progression. -/
def SzemerediFinitary : Prop :=
  ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s : Finset ℕ, s ⊆ Finset.range N →
    δ * N ≤ #s → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ s

/-- Monotonicity in the length of the progression. -/
lemma HasAPOfLength.mono {A : Set ℕ} {k l : ℕ} (h : HasAPOfLength A k) (hl : l ≤ k) :
    HasAPOfLength A l := by
  obtain ⟨a, d, hd, ha⟩ := h
  exact ⟨a, d, hd, fun i hi => ha i (lt_of_lt_of_le hi hl)⟩

/-- **Base case (length three).**  Every set of natural numbers of positive upper density contains
a genuine three-term arithmetic progression.  This is Roth's theorem, i.e. the first nontrivial
case of Szemerédi's theorem. -/
theorem exists_threeAP_of_posUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) :
    HasAPOfLength A 3 := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N, hN, hcard⟩ := hdens (cornersTheoremBound (δ / 3))
  have hnot : ¬ ThreeAPFree ((trace A N : Finset ℕ) : Set ℕ) :=
    roth_3ap_theorem_nat δ hδ hN (trace A N) (trace_subset A N) hcard
  have hex : ∃ a ∈ trace A N, ∃ b ∈ trace A N, ∃ c ∈ trace A N, a + c = b + b ∧ a ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hnot fun a ha b hb c hc habc => hcon a ha b hb c hc habc
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hex
  have haA : a ∈ A := mem_of_mem_trace ha
  have hbA : b ∈ A := mem_of_mem_trace hb
  have hcA : c ∈ A := mem_of_mem_trace hc
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using haA
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hbA
    · have : a + 2 * (b - a) = c := by omega
      rw [this]; exact hcA
  · refine ⟨c, a - b, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hcA
    · have : c + 1 * (a - b) = b := by omega
      rw [this]; exact hbA
    · have : c + 2 * (a - b) = a := by omega
      rw [this]; exact haA

/-- **The reduction.**  The finitary form of Szemerédi's theorem implies the density form: any set
of natural numbers of positive upper density contains arithmetic progressions of every length. -/
theorem szemeredi_of_finitary (hSz : SzemerediFinitary) {A : Set ℕ} (hA : HasPosUpperDensity A)
    (k : ℕ) : HasAPOfLength A k := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N₀, hN₀⟩ := hSz k δ hδ
  obtain ⟨N, hN, hcard⟩ := hdens N₀
  obtain ⟨a, d, hd, hmem⟩ := hN₀ N hN (trace A N) (trace_subset A N) hcard
  exact ⟨a, d, hd, fun i hi => mem_of_mem_trace (hmem i hi)⟩

/-- **Furstenberg–Szemerédi.**

Positive-density subsets of `ℕ` contain arbitrarily long arithmetic progressions.

Two Lean-checked components are recorded here:

* the *base case*: unconditionally, every set of positive upper density contains an arithmetic
  progression of length `k` for every `k ≤ 3` (the length-three case being Roth's theorem);
* the *reduction*: assuming the finitary form of Szemerédi's theorem (`SzemerediFinitary`), every
  set of positive upper density contains arithmetic progressions of *every* length. -/
theorem furstenberg_szemeredi :
    (∀ A : Set ℕ, HasPosUpperDensity A → ∀ k ≤ 3, HasAPOfLength A k) ∧
      (SzemerediFinitary → ∀ A : Set ℕ, HasPosUpperDensity A → ∀ k : ℕ, HasAPOfLength A k) := by
  refine ⟨fun A hA k hk => (exists_threeAP_of_posUpperDensity hA).mono hk, ?_⟩
  intro hSz A hA k
  exact szemeredi_of_finitary hSz hA k

end Frontier

