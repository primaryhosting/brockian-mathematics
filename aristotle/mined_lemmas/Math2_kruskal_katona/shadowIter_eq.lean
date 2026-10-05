import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
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

set_option grind.warning false

namespace Math2

open Finset

variable {n : ℕ}

/-- The shadow of a family `𝒜` of finite sets: all the sets obtained from a member of `𝒜` by
deleting one element. -/

lemma shadowIter_eq (i : ℕ) (𝒜 : Finset (Finset (Fin n))) :
    shadowIter i 𝒜 = (Finset.shadow)^[i] 𝒜 := rfl

/-- **The Lovász form of the Kruskal–Katona theorem.**

If `𝒜` is a family of `r`-element subsets of `Fin n` with `k.choose r ≤ #𝒜` (where
`i ≤ r ≤ k ≤ n`), then its `i`-th iterated shadow has at least `k.choose (r - i)` elements. -/
