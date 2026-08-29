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

/-- `countUpTo A N` is the number of elements of `A` below `N`. -/

theorem exists_density_windows (A : Set ℕ) (h : 0 < upperDensity A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ δ * (N : ℝ) ≤ (countUpTo A N : ℝ) := by
  set f : ℕ → ℝ := fun N => (countUpTo A N : ℝ) / N with hf
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop f :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop hnn
  set c : ℝ := upperDensity A with hc
  have hfreq : ∃ᶠ N in Filter.atTop, c / 2 < f N := by
    apply Filter.frequently_lt_of_lt_limsup hcob
    have : Filter.limsup f Filter.atTop = c := rfl
    rw [this]
    linarith
  refine ⟨c / 2, by linarith, ?_⟩
  intro M
  obtain ⟨N, hlt, hN⟩ := (hfreq.and_eventually (Filter.eventually_ge_atTop (max M 1))).exists
  refine ⟨N, le_trans (le_max_left _ _) hN, ?_⟩
  have hN1 : (1 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have h2 : c / 2 * (N : ℝ) < (countUpTo A N : ℝ) :=
    (lt_div_iff₀ hNpos).mp (by simpa [hf] using hlt)
  linarith

/-- A set of positive upper density is infinite. -/
