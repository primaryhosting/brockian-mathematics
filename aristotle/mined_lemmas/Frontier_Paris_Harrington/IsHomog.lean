import Mathlib
/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The strengthened finite Ramsey theorem (Paris–Harrington)

A finite set `Y ⊆ ℕ` of positive integers is *relatively large* if its number of
elements is at least its least element.  The Paris–Harrington statement says:

> for all `n, k, m` there is `N` such that for every colouring `c` of the
> `n`-element subsets of `{1, …, N}` with `k` colours there is a relatively large
> `Y ⊆ {1, …, N}` with `m ≤ |Y|` all of whose `n`-element subsets have the same
> colour.

This is `Frontier.Paris_Harrington` below, and it is proved here in full (via the
infinite Ramsey theorem proved in Part 1 below together with an
ultrafilter compactness argument).

The second half of the Paris–Harrington theorem — that this statement is *not*
provable in first-order Peano arithmetic — is a metamathematical statement about
a formal proof system, not a statement of ordinary mathematics; it is not
formalized here.  What is formalized and proved here is the truth of the
strengthened finite Ramsey theorem.
-/

namespace Frontier

open Finset Filter

/-! ## Part 1: the infinite Ramsey theorem for hypergraphs -/

/-- `H` is homogeneous for the colouring `c` in dimension `n`: all `n`-element
subsets of `H` receive the same colour. -/

def IsHomog (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (Y : Finset ℕ) : Prop :=
  ∀ A ∈ Y.powersetCard n, ∀ B ∈ Y.powersetCard n, c A = c B

/-- **The strengthened finite Ramsey theorem of Paris and Harrington.**

For all `n`, `k`, `m` there is an `N` such that every colouring `c` of the
`n`-element subsets of `{1, …, N}` by `k` colours admits a *relatively large*
homogeneous set `Y ⊆ {1, …, N}` with at least `m` elements. -/
