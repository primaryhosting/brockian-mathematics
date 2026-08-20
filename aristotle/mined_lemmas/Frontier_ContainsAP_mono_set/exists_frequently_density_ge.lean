import Mathlib
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module docstring above is placed immediately after `import Mathlib`.

## Contents

* `Frontier.ContainsAP A k` : the set `A ⊆ ℕ` contains an arithmetic progression of length `k`
  with positive common difference.
* `Frontier.upperDensity A` : the upper asymptotic density of `A ⊆ ℕ`.
* `Frontier.FinitarySzemeredi k` : the finitary form of Szemerédi's theorem for progressions of
  length `k`.
* `Frontier.furstenberg_szemeredi` : the reduction of Szemerédi's theorem (positive upper density
  sets of naturals contain arbitrarily long arithmetic progressions) to its finitary form.
* `Frontier.finitarySzemeredi_three` : the finitary statement for `k = 3`, deduced from Roth's
  theorem (available in Mathlib as `roth_3ap_theorem_nat`).
* `Frontier.furstenberg_szemeredi_three` : the resulting *unconditional* base case: every set of
  naturals of positive upper density contains a 3-term arithmetic progression.
-/

open Filter Finset

open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that `A` contains an arithmetic progression of length `k` with
positive common difference. -/

lemma exists_frequently_density_ge {A : Set ℕ} (hA : 0 < upperDensity A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧
      δ * n ≤ (((Finset.range n).filter (fun x => x ∈ A)).card : ℝ) := by
  set δ := upperDensity A / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (densityUpTo A) := by
    refine ⟨0, fun a ha => ?_⟩
    rw [eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact (densityUpTo_nonneg A n).trans hn
  have hlt : δ < limsup (densityUpTo A) atTop := by
    rw [← upperDensity]; linarith
  have hfreq : ∃ᶠ n in atTop, δ < densityUpTo A n :=
    Filter.frequently_lt_of_lt_limsup hcobdd hlt
  refine ⟨δ, hδ, fun N => ?_⟩
  obtain ⟨n, hnN, hn⟩ := (hfreq.and_eventually (eventually_ge_atTop N)).exists
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [densityUpTo] at hnN; linarith
    · exact hn0
  refine ⟨n, hn, hnpos, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [densityUpTo, lt_div_iff₀ hn'] at hnN
  linarith

/-- The finitary form of Szemerédi's theorem for progressions of length `k`: for every positive
density `δ` there is an `N` such that every subset of `{0, ..., n - 1}` of size at least `δ * n`,
with `n ≥ N`, contains a `k`-term arithmetic progression. -/
