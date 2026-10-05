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
