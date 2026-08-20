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

/-- `A ⊆ ℕ` has positive upper (Banach-type) density: there is `δ > 0` such that for
arbitrarily large `M` the initial segment `{0, …, M-1}` meets `A` in at least `δ * M` points. -/

def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    δ * M ≤ (((Finset.range M).filter (fun n => n ∈ A)).card : ℝ)

/-- `A` contains an arithmetic progression of length `k` (with positive common difference). -/

def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The finitary form of Szemerédi's theorem: for every length `k` and density `δ > 0`,
every sufficiently large initial segment `{0, …, N-1}` has the property that each of its
subsets of size at least `δ * N` contains an arithmetic progression of length `k`. -/

def SzemerediFinitary : Prop :=
  ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ,
    S ⊆ Finset.range N → δ * N ≤ (S.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- Containing a long progression is stronger than containing a short one. -/

theorem ContainsAP.mono {A : Set ℕ} {k l : ℕ} (h : ContainsAP A k) (hl : l ≤ k) :
    ContainsAP A l := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (lt_of_lt_of_le hi hl)⟩

/-- A set of positive upper density is unbounded. -/

theorem furstenberg_szemeredi (hSz : SzemerediFinitary) {A : Set ℕ}
    (hA : HasPositiveUpperDensity A) (k : ℕ) : ContainsAP A k := by
  obtain ⟨δ, hδ, hden⟩ := hA
  obtain ⟨N₀, hN₀⟩ := hSz k δ hδ
  obtain ⟨M, hM₀, hM⟩ := hden N₀
  obtain ⟨a, d, hd, hap⟩ :=
    hN₀ M hM₀ ((Finset.range M).filter (fun n => n ∈ A)) (Finset.filter_subset _ _) hM
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have := hap i hi
  simp only [Finset.mem_filter] at this
  exact this.2

end Frontier
