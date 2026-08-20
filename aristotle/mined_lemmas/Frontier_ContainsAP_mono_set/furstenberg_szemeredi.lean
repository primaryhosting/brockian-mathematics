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

theorem furstenberg_szemeredi (k : ℕ) (hk : FinitarySzemeredi k) (A : Set ℕ)
    (hA : 0 < upperDensity A) : ContainsAP A k := by
  obtain ⟨δ, hδ, hfreq⟩ := exists_frequently_density_ge hA
  obtain ⟨N, hN⟩ := hk δ hδ
  obtain ⟨n, hnN, _, hcard⟩ := hfreq N
  have := hN n hnN ((Finset.range n).filter (fun x => x ∈ A)) (Finset.filter_subset _ _) hcard
  refine this.mono_set ?_
  intro x hx
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
  exact hx.2

/-- Failure of `ThreeAPFree` produces a genuine 3-term arithmetic progression with positive
common difference. -/
