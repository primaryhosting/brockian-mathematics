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

open Filter Finset

namespace Frontier

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

theorem hasAP_three_of_pos_upperDensity (A : Set ℕ) (hA : 0 < upperDensity A) : HasAP A 3 := by
  classical
  set c : ℝ := upperDensity A / 2 with hc
  have hc0 : 0 < c := by positivity
  have hclt : c < upperDensity A := by rw [hc]; linarith
  have hroth : ∀ᶠ n : ℕ in atTop, (rothNumberNat n : ℝ) ≤ (c / 2) * n := by
    have := (Asymptotics.isLittleO_iff.1 rothNumberNat_isLittleO_id) (by positivity : (0:ℝ) < c / 2)
    filter_upwards [this] with n hn
    simpa [abs_of_nonneg, Nat.cast_nonneg] using hn
  obtain ⟨n, hn, hrn⟩ := ((frequently_lt_countUpTo hclt).and_eventually hroth).exists
  set s : Finset ℕ := (Finset.range n).filter (· ∈ A) with hs
  have hsub : s ⊆ Finset.range n := Finset.filter_subset _ _
  have hcards : (countUpTo A n : ℝ) = (s.card : ℝ) := by simp [hs, countUpTo]
  have hnpos : (0:ℝ) < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [countUpTo] at hn
    · exact_mod_cast hpos
  have hlt : (rothNumberNat n : ℝ) < (s.card : ℝ) := by
    have hhalf : (c / 2) * n < c * n := by nlinarith
    linarith [hcards ▸ hn]
  obtain ⟨a, d, hd, h0, h1, h2⟩ :=
    exists_threeAP_of_rothNumberNat_lt hsub (by exact_mod_cast hlt)
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hmem : ∀ x ∈ s, x ∈ A := by
    intro x hx
    exact (Finset.mem_filter.1 hx).2
  interval_cases i
  · simpa using hmem a h0
  · simpa using hmem _ h1
  · simpa using hmem _ h2

/-- Unconditionally, a set of positive upper density contains arithmetic progressions of
every length `k ≤ 3`. -/
