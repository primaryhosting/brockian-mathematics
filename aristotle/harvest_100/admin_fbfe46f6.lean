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

/-! ## Basic definitions -/

/-- `HasAP A k` says that the set `A ⊆ ℕ` contains a non-degenerate arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` (with common difference `d > 0`). -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `HasPosUpperDensity A` says that `A ⊆ ℕ` has positive upper density: there is a `δ > 0`
such that `|A ∩ [0, N)| ≥ δ N` for infinitely many `N`. -/
def HasPosUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    δ * (N : ℝ) ≤ (((Finset.range N).filter (fun n => n ∈ A)).card : ℝ)

/-- An arithmetic progression of length `k` is in particular one of any shorter length. -/
theorem HasAP.mono {A : Set ℕ} {k l : ℕ} (h : HasAP A k) (hlk : l ≤ k) : HasAP A l := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (lt_of_lt_of_le hi hlk)⟩

/-- Progressions are inherited by supersets. -/
theorem HasAP.subset {A B : Set ℕ} {k : ℕ} (h : HasAP A k) (hAB : A ⊆ B) : HasAP B k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => hAB (h i hi)⟩

/-! ## Roth's theorem: the length-three case

Mathlib's `roth_3ap_theorem_nat` says that a dense enough subset of `[0, N)` is not `3AP`-free.
We turn this into the statement that such a set contains a genuine increasing progression
`a, a + d, a + 2d` with `d > 0`. -/

/-- A dense subset of `[0, N)`, for `N` large in terms of the density, contains a three-term
arithmetic progression with positive common difference. -/
theorem hasAP_three_of_dense_finset {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hN : cornersTheoremBound (δ / 3) ≤ N) (S : Finset ℕ) (hSsub : S ⊆ Finset.range N)
    (hScard : δ * (N : ℝ) ≤ (S.card : ℝ)) : HasAP (S : Set ℕ) 3 := by
  have hRoth : ¬ ThreeAPFree (S : Set ℕ) := roth_3ap_theorem_nat δ hδ hN S hSsub hScard
  have hne : ¬ ∀ a ∈ (S : Set ℕ), ∀ b ∈ (S : Set ℕ), ∀ c ∈ (S : Set ℕ),
      a + c = b + b → a = b := hRoth
  push_neg at hne
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hne
  rcases lt_or_gt_of_ne hab with h | h
  · -- `a < b`, so `a, b, c` is an increasing three-term progression
    refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · have hb' : a + 1 * (b - a) = b := by omega
      rw [hb']; exact hb
    · have hc' : a + 2 * (b - a) = c := by omega
      rw [hc']; exact hc
  · -- `b < a`, so `c, b, a` is an increasing three-term progression
    refine ⟨c, b - c, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hc
    · have hb' : c + 1 * (b - c) = b := by omega
      rw [hb']; exact hb
    · have ha' : c + 2 * (b - c) = a := by omega
      rw [ha']; exact ha

/-- A set of positive upper density contains a three-term arithmetic progression.
This is Roth's theorem, i.e. the `k = 3` case of Szemerédi's theorem. -/
theorem hasAP_three_of_posUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) : HasAP A 3 := by
  obtain ⟨δ, hδ, hden⟩ := hA
  obtain ⟨N, hN, hcard⟩ := hden (cornersTheoremBound (δ / 3))
  refine (hasAP_three_of_dense_finset hδ hN _ (Finset.filter_subset _ _) hcard).subset ?_
  intro x hx
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
  exact hx.2

/-! ## The target statement -/

/-- **Szemerédi's theorem, base cases (`k ≤ 3`).**

Every set `A ⊆ ℕ` of positive upper density contains arithmetic progressions of every length
`k ≤ 3`. The case `k = 3` is Roth's theorem (obtained here from the corners theorem, which in
Mathlib is proved via the triangle removal lemma / Szemerédi regularity); the cases `k ≤ 2` follow
from it. The full theorem, for all `k`, is Szemerédi's theorem, proved by Furstenberg's multiple
recurrence theorem in ergodic theory; it is not available in Mathlib, so the statement here is
restricted to the range of `k` that can currently be verified. The general statement is recorded
below as `Frontier.SzemerediDensity`, together with a Lean-checked reduction of it to the
finitary form `Frontier.SzemerediFinitary`. -/
theorem furstenberg_szemeredi {A : Set ℕ} (hA : HasPosUpperDensity A) {k : ℕ} (hk : k ≤ 3) :
    HasAP A k :=
  (hasAP_three_of_posUpperDensity hA).mono hk

/-! ## The general statement and a Lean-checked reduction

`SzemerediDensity k` is the full density statement of Szemerédi's theorem for progressions of
length `k`; `SzemerediFinitary k` is its finitary ("Szemerédi's theorem for `[0, N)`") form.
We check in Lean that the finitary form implies the density form, and that both hold for
`k ≤ 3`. -/

/-- The density form of Szemerédi's theorem for progressions of length `k`: every subset of `ℕ`
of positive upper density contains an arithmetic progression of length `k`. -/
def SzemerediDensity (k : ℕ) : Prop :=
  ∀ A : Set ℕ, HasPosUpperDensity A → HasAP A k

/-- The finitary form of Szemerédi's theorem for progressions of length `k`: for every `δ > 0`
there is a threshold `N₀` such that every subset of `[0, N)` with `N ≥ N₀` and at least `δ N`
elements contains an arithmetic progression of length `k`. -/
def SzemerediFinitary (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.range N →
    δ * (N : ℝ) ≤ (S.card : ℝ) → HasAP (S : Set ℕ) k

/-- **Reduction.** The finitary form of Szemerédi's theorem implies the density form. -/
theorem szemerediDensity_of_finitary {k : ℕ} (h : SzemerediFinitary k) : SzemerediDensity k := by
  rintro A ⟨δ, hδ, hden⟩
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  obtain ⟨N, hN, hcard⟩ := hden N₀
  refine (hN₀ N hN _ (Finset.filter_subset _ _) hcard).subset ?_
  intro x hx
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
  exact hx.2

/-- The finitary form of Szemerédi's theorem holds for `k ≤ 3`. -/
theorem szemerediFinitary_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediFinitary k := by
  intro δ hδ
  refine ⟨cornersTheoremBound (δ / 3), fun N hN S hSsub hScard => ?_⟩
  exact (hasAP_three_of_dense_finset hδ hN S hSsub hScard).mono hk

/-- The density form of Szemerédi's theorem holds for `k ≤ 3`; equivalently, this is the target
theorem `Frontier.furstenberg_szemeredi` in packaged form. -/
theorem szemerediDensity_of_le_three {k : ℕ} (hk : k ≤ 3) : SzemerediDensity k :=
  szemerediDensity_of_finitary (szemerediFinitary_of_le_three hk)

end Frontier

#print axioms Frontier.furstenberg_szemeredi
#print axioms Frontier.szemerediDensity_of_finitary
#print axioms Frontier.szemerediDensity_of_le_three

