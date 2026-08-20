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

theorem exists_mem_ge_of_hasPositiveUpperDensity {A : Set ℕ} (hA : HasPositiveUpperDensity A)
    (N : ℕ) : ∃ m : ℕ, N ≤ m ∧ m ∈ A := by
  obtain ⟨δ, hδ, h⟩ := hA
  -- choose a scale `K` at which the density bound already forces more than `N` elements
  obtain ⟨K, hK⟩ := exists_nat_gt ((N + 1 : ℝ) / δ)
  obtain ⟨M, hMK, hM⟩ := h K
  have hKM : ((K : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hMK
  have hlt : ((N : ℝ) + 1) < δ * K := by
    have := (div_lt_iff₀ hδ).mp hK
    linarith [this]
  have hcard : ((N : ℝ) + 1) < (((Finset.range M).filter (fun n => n ∈ A)).card : ℝ) := by
    have : δ * (K : ℝ) ≤ δ * (M : ℝ) := by
      exact mul_le_mul_of_nonneg_left hKM (le_of_lt hδ)
    linarith
  have hcardN : N < ((Finset.range M).filter (fun n => n ∈ A)).card := by
    have : (N : ℝ) < (((Finset.range M).filter (fun n => n ∈ A)).card : ℝ) := by linarith
    exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  -- otherwise every element of `A` lies below `N`, bounding the count by `N`
  have hsub : ((Finset.range M).filter (fun n => n ∈ A)) ⊆ Finset.range N := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    by_contra hxN
    exact absurd hx.2 (hcon x (by omega))
  have := Finset.card_le_card hsub
  simp only [Finset.card_range] at this
  omega

/-- Base case: a set of positive upper density contains a two-term arithmetic progression.
(This is unconditional; no form of Szemerédi's theorem is used.) -/
