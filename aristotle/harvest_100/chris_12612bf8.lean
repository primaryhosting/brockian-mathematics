/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped FinsetFamily

namespace Math2

/-- The **Kruskal–Katona theorem**.

Given a set family `𝒜` of `r`-element subsets of `Fin n`, and `𝒞` an initial segment of the
colex order consisting of `r`-sets with `𝒞.card ≤ 𝒜.card`, the shadow of `𝒞` is no larger than the
shadow of `𝒜`. In other words, the minimum possible shadow size for a family of `r`-sets of a
given cardinality is attained by initial segments of the colex order.

This restates `Finset.kruskal_katona` from
`Mathlib.Combinatorics.SetFamily.KruskalKatona`. -/
theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : 𝒞.card ≤ 𝒜.card)
    (h𝒞 : Finset.Colex.IsInitSeg 𝒞 r) : (∂ 𝒞).card ≤ (∂ 𝒜).card :=
  Finset.kruskal_katona h𝒜r h𝒞𝒜 h𝒞

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

