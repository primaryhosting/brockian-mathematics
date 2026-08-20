/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not permit a module docstring `/-! ... -/` before `import`, so the required
-- header is reproduced verbatim above as an ordinary block comment.)

import Mathlib

open Finset
open scoped FinsetFamily

namespace Math2

/-- The **Kruskal–Katona theorem**.

Given a family `𝒜` of `r`-element subsets of `Fin n`, and a family `𝒞` which is an initial
segment of the colexicographic order on `r`-sets with `#𝒞 ≤ #𝒜`, the shadow of `𝒞` is no
bigger than the shadow of `𝒜`. In other words, among families of `r`-sets of a given size,
the minimum shadow size is attained by initial segments of colex.

This is Mathlib's `Finset.kruskal_katona`
(`Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`), which we cite here. -/
theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : #𝒞 ≤ #𝒜)
    (h𝒞 : Finset.Colex.IsInitSeg 𝒞 r) :
    #(∂ 𝒞) ≤ #(∂ 𝒜) :=
  Finset.kruskal_katona h𝒜r h𝒞𝒜 h𝒞

/-- The Lovász form of the Kruskal–Katona theorem: if `𝒜` is a family of `r`-sets in `Fin n`
with `#𝒜 ≥ k.choose r` (where `i ≤ r ≤ k ≤ n`), then its `i`-th iterated shadow has size at
least `k.choose (r - i)`. This is Mathlib's `Finset.kruskal_katona_lovasz_form`. -/
theorem kruskal_katona_lovasz_form {n r k i : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) :=
  Finset.kruskal_katona_lovasz_form hir hrk hkn h𝒜r hcard

end Math2

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

