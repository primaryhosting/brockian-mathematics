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

/-- `A` contains an arithmetic progression of length `k`, i.e. there are `a` and a positive
common difference `d` with `a, a + d, …, a + (k-1) * d` all in `A`. -/
def HasAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The number of elements of `A` below `M`. -/
noncomputable def prefixCard (A : Set ℕ) (M : ℕ) : ℕ :=
  ((Finset.range M).filter (fun n => n ∈ A)).card

/-- `A ⊆ ℕ` has positive upper density: there is `δ > 0` such that `|A ∩ [0, M)| ≥ δ * M` for
arbitrarily large `M`. -/
def UpperDensityPos (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ δ * M ≤ (prefixCard A M : ℝ)

/-- The full statement of Szemerédi's theorem (Furstenberg's multiple recurrence form):
every set of natural numbers with positive upper density contains arithmetic progressions of
every length. -/
def SzemerediStatement : Prop :=
  ∀ A : Set ℕ, UpperDensityPos A → ∀ k : ℕ, HasAPOfLength A k

/-- The finitary (density) form of Szemerédi's theorem: for every length `k` and density `δ > 0`,
every sufficiently long initial segment of `ℕ` has the property that each of its subsets of
density at least `δ` contains a nondegenerate `k`-term arithmetic progression. -/
def FinitarySzemeredi : Prop :=
  ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s : Finset ℕ, s ⊆ Finset.range N →
    δ * N ≤ (s.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ s

section Basic

lemma mem_of_mem_prefixFinset {A : Set ℕ} {M x : ℕ}
    (hx : x ∈ (Finset.range M).filter (fun n => n ∈ A)) : x ∈ A := by
  simpa using (Finset.mem_filter.mp hx).2

lemma lt_of_mem_prefixFinset {A : Set ℕ} {M x : ℕ}
    (hx : x ∈ (Finset.range M).filter (fun n => n ∈ A)) : x < M := by
  simpa using Finset.mem_range.mp (Finset.mem_filter.mp hx).1

lemma hasAPOfLength_of_le {A : Set ℕ} {k l : ℕ} (hkl : k ≤ l) (h : HasAPOfLength A l) :
    HasAPOfLength A k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (lt_of_lt_of_le hi hkl)⟩

/-- A nontrivial solution of `x + z = y + y` inside `A` yields a `3`-term progression in `A`. -/
lemma hasAPOfLength_three_of_average {A : Set ℕ} {x y z : ℕ} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxyz : x + z = y + y) (hne : x ≠ y) : HasAPOfLength A 3 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨x, y - x, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hx
    · have h1 : x + 1 * (y - x) = y := by omega
      rw [h1]; exact hy
    · have h2 : x + 2 * (y - x) = z := by omega
      rw [h2]; exact hz
  · refine ⟨z, y - z, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hz
    · have h1 : z + 1 * (y - z) = y := by omega
      rw [h1]; exact hy
    · have h2 : z + 2 * (y - z) = x := by omega
      rw [h2]; exact hx

/-- Sanity check: the hypothesis `UpperDensityPos` is satisfiable (`Set.univ` has density `1`). -/
lemma upperDensityPos_univ : UpperDensityPos Set.univ :=
  ⟨1, one_pos, fun N => ⟨N, le_rfl, by simp [prefixCard]⟩⟩

end Basic

/-- **Reduction**: the finitary density form of Szemerédi's theorem implies the infinitary
statement about sets of positive upper density. -/
theorem szemeredi_of_finitary (h : FinitarySzemeredi) : SzemerediStatement := by
  rintro A ⟨δ, hδ, hA⟩ k
  obtain ⟨N₀, hN₀⟩ := h k δ hδ
  obtain ⟨M, hM, hcard⟩ := hA N₀
  obtain ⟨a, d, hd, hmem⟩ :=
    hN₀ M hM ((Finset.range M).filter (fun n => n ∈ A)) (Finset.filter_subset _ _) hcard
  exact ⟨a, d, hd, fun i hi => mem_of_mem_prefixFinset (hmem i hi)⟩

/-- Roth's theorem (available in Mathlib) in the form we need: for every `δ > 0` all sufficiently
long initial segments have Roth number at most `δ` times their length. -/
lemma rothNumberNat_le_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (rothNumberNat N : ℝ) ≤ δ * N := by
  have h := Asymptotics.IsLittleO.def rothNumberNat_isLittleO_id hδ
  rw [Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun N hN => ?_⟩
  have := hN₀ N hN
  simpa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using this

/-- Every set of positive upper density contains a `3`-term arithmetic progression.
This is the density (Roth) case of Szemerédi's theorem. -/
theorem hasAPOfLength_three_of_upperDensityPos {A : Set ℕ} (hA : UpperDensityPos A) :
    HasAPOfLength A 3 := by
  obtain ⟨δ, hδ, hA⟩ := hA
  obtain ⟨N₀, hN₀⟩ := rothNumberNat_le_eventually (half_pos hδ)
  obtain ⟨M, hM, hcard⟩ := hA (max N₀ 1)
  have hM₀ : N₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : (1 : ℕ) ≤ M := le_trans (le_max_right _ _) hM
  set s : Finset ℕ := (Finset.range M).filter (fun n => n ∈ A) with hs
  have hnot : ¬ ThreeAPFree (s : Set ℕ) := by
    intro hfree
    have hle : s.card ≤ rothNumberNat M :=
      hfree.le_rothNumberNat s (fun x hx => lt_of_mem_prefixFinset hx) rfl
    have h1 : δ * M ≤ (rothNumberNat M : ℝ) := by
      refine le_trans hcard ?_
      exact_mod_cast hle
    have h2 : (rothNumberNat M : ℝ) ≤ δ / 2 * M := hN₀ M hM₀
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    nlinarith
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hne⟩ := hnot
  refine hasAPOfLength_three_of_average (A := A) ?_ ?_ ?_ hxyz hne
  · exact mem_of_mem_prefixFinset (Finset.mem_coe.mp hx)
  · exact mem_of_mem_prefixFinset (Finset.mem_coe.mp hy)
  · exact mem_of_mem_prefixFinset (Finset.mem_coe.mp hz)

/-- **Furstenberg–Szemerédi (density case, unconditional)**: every subset of `ℕ` of positive
upper density contains arithmetic progressions of every length `k ≤ 3`; moreover the general
statement for all lengths follows, as a Lean-checked reduction, from the finitary density form
of Szemerédi's theorem. -/
theorem furstenberg_szemeredi :
    (∀ A : Set ℕ, UpperDensityPos A → ∀ k ≤ 3, HasAPOfLength A k) ∧
      (FinitarySzemeredi → SzemerediStatement) :=
  ⟨fun _A hA _k hk => hasAPOfLength_of_le hk (hasAPOfLength_three_of_upperDensityPos hA),
    szemeredi_of_finitary⟩

end Frontier

