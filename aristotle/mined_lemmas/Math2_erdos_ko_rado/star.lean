/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Math2

/-- The **Erdős–Ko–Rado theorem** for families of subsets of `[n] = {0, 1, ..., n-1}`.

If `𝒜` is a family of `k`-element subsets of `Finset.range n` that is intersecting (any two
members, including a member with itself, meet), and `n ≥ 2 * k`, then `#𝒜 ≤ (n-1).choose (k-1)`.

The proof transfers the statement to `Finset (Fin n)` and applies Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/

def star (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range n).powersetCard k).filter (fun A => 0 ∈ A)

