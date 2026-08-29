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
