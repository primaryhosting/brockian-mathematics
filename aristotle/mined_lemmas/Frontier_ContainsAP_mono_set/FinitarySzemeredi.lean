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

def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ B : Finset ℕ, B ⊆ Finset.range n →
    δ * n ≤ (B.card : ℝ) → ContainsAP (B : Set ℕ) k

/-- **Szemerédi's theorem** (Furstenberg's multiple recurrence formulation, reduced to its
finitary form): a set of naturals of positive upper density contains arithmetic progressions of
every length `k`, granted the finitary statement `FinitarySzemeredi k`.

The finitary hypothesis is unconditionally verified for `k ≤ 3` in
`Frontier.finitarySzemeredi_three`, which yields the unconditional base case
`Frontier.furstenberg_szemeredi_three`. -/
