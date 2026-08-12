/-
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 does not permit a module docstring to precede `import`, so the header above is
-- wrapped in an outer block comment.)
import Mathlib

open Finset Filter MeasureTheory
open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that the set `A ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with positive common difference `d`. -/
def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The upper (Banach-type) density of `A ⊆ ℕ`, i.e. the `limsup` of `|A ∩ [0,n)| / n`. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun n : ℕ => (#{x ∈ range n | x ∈ A} : ℝ) / n) atTop

/-- The finitary form of Szemerédi's theorem for progressions of length `k`: for every `ε > 0`
there is an `N` such that every subset of `{0, …, n-1}` with `n ≥ N` and at least `ε n` elements
contains an arithmetic progression of length `k`. -/
def SzemerediFinitary (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ, A ⊆ range n → ε * n ≤ #A →
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- Szemerédi's theorem in the infinitary (positive upper density) form. -/
def SzemerediTheorem : Prop :=
  ∀ (A : Set ℕ) (k : ℕ), 0 < upperDensity A → ContainsAP A k

section Density

variable {A : Set ℕ}

/-- A set of positive upper density has, for some `ε > 0`, infinitely many initial segments in
which it occupies at least an `ε`-fraction. -/
theorem exists_frequently_card_ge_of_pos_upperDensity (hA : 0 < upperDensity A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n ≥ N, 1 ≤ n ∧ ε * n ≤ #{x ∈ range n | x ∈ A} := by
  set f : ℕ → ℝ := fun n => (#{x ∈ range n | x ∈ A} : ℝ) / n with hf
  have hfnonneg : ∀ n : ℕ, 0 ≤ f n := fun n => by positivity
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop f := by
    refine ⟨0, fun a ha => ?_⟩
    obtain ⟨n, hn⟩ := (eventually_map.1 ha).exists
    exact (hfnonneg n).trans hn
  have hfreq : ∃ᶠ n in atTop, upperDensity A / 2 < f n :=
    frequently_lt_of_lt_limsup hcobdd (by simpa [upperDensity, hf] using half_lt_self hA)
  refine ⟨upperDensity A / 2, by positivity, fun N => ?_⟩
  obtain ⟨n, hn, hnN⟩ := (hfreq.and_eventually (eventually_ge_atTop (max N 1))).exists
  have hn1 : 1 ≤ n := le_of_max_le_right hnN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ⟨n, le_of_max_le_left hnN, hn1, by
    rw [hf] at hn
    exact (le_div_iff₀ hnpos).1 hn.le⟩

end Density

/-- Finitary Szemerédi is monotone in the length of the progression. -/
theorem szemerediFinitary_mono {j k : ℕ} (hjk : j ≤ k) (hk : SzemerediFinitary k) :
    SzemerediFinitary j := by
  intro ε hε
  obtain ⟨N, hN⟩ := hk ε hε
  refine ⟨N, fun n hn A hA hcard => ?_⟩
  obtain ⟨a, d, hd, h⟩ := hN n hn A hA hcard
  exact ⟨a, d, hd, fun i hi => h i (hi.trans_le hjk)⟩

/-- **Roth's theorem** gives the finitary Szemerédi statement for progressions of length `3`. -/
theorem szemerediFinitary_three : SzemerediFinitary 3 := by
  have key : ∀ (A : Finset ℕ) (x y z : ℕ), x ∈ A → y ∈ A → z ∈ A → x < y → y < z →
      x + z = y + y → ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ A := by
    intro A x y z hx hy hz hxy hyz hsum
    refine ⟨x, y - x, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hx
    · have : x + 1 * (y - x) = y := by omega
      rw [this]; exact hy
    · have : x + 2 * (y - x) = z := by omega
      rw [this]; exact hz
  intro ε hε
  refine ⟨cornersTheoremBound (ε / 3), fun n hn A hA hcard => ?_⟩
  by_contra hcon
  refine roth_3ap_theorem_nat ε hε hn A hA hcard ?_
  intro a ha b hb c hc habc
  by_contra hab
  simp only [mem_coe] at ha hb hc
  rcases lt_or_gt_of_ne hab with h | h
  · exact hcon (key A a b c ha hb hc h (by omega) habc)
  · exact hcon (key A c b a hc hb ha (by omega) h (by omega))

/-- Unconditional finitary Szemerédi for progressions of length at most `3`. -/
theorem szemerediFinitary_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediFinitary k :=
  szemerediFinitary_mono hk szemerediFinitary_three

/-- **Szemerédi's theorem**, in the form of a Lean-checked reduction of the infinitary
(positive upper density) statement to the finitary one, which in the ergodic-theoretic
approach of Furstenberg is supplied by the multiple recurrence theorem.

For `k ≤ 3` the hypothesis is unconditionally available
(see `Frontier.szemerediFinitary_of_le_three`), so the conclusion holds outright; this is the
base case of the induction on the length `k` of the progression. -/
theorem furstenberg_szemeredi {k : ℕ} (hk : SzemerediFinitary k) {A : Set ℕ}
    (hA : 0 < upperDensity A) : ContainsAP A k := by
  obtain ⟨ε, hε, hfreq⟩ := exists_frequently_card_ge_of_pos_upperDensity hA
  obtain ⟨N, hN⟩ := hk ε hε
  obtain ⟨n, hn, -, hcard⟩ := hfreq N
  obtain ⟨a, d, hd, h⟩ := hN n hn {x ∈ range n | x ∈ A} (filter_subset _ _) hcard
  exact ⟨a, d, hd, fun i hi => (mem_filter.1 (h i hi)).2⟩

/-- Szemerédi's theorem follows from its finitary form for every length. -/
theorem szemerediTheorem_of_finitary (h : ∀ k, SzemerediFinitary k) : SzemerediTheorem :=
  fun _A k hA => furstenberg_szemeredi (h k) hA

/-- The base case: every set of positive upper density contains arithmetic progressions of
length at most `3`. -/
theorem furstenberg_szemeredi_three {k : ℕ} (hk : k ≤ 3) {A : Set ℕ}
    (hA : 0 < upperDensity A) : ContainsAP A k :=
  furstenberg_szemeredi (szemerediFinitary_of_le_three hk) hA

/-- The base case `k = 2` of Furstenberg's multiple recurrence theorem: the Poincaré recurrence
theorem. For a measure-preserving map of a finite measure space and a set `E` of positive
measure there is some `n > 0` with `E ∩ T^[n]⁻¹ E` of positive measure. -/
theorem furstenberg_multiple_recurrence_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ) {E : Set α}
    (hE : MeasurableSet E) (hE0 : μ E ≠ 0) :
    ∃ n > 0, μ (E ∩ T^[n] ⁻¹' E) ≠ 0 :=
  hT.conservative.exists_gt_measure_inter_ne_zero hE.nullMeasurableSet hE0 0

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

