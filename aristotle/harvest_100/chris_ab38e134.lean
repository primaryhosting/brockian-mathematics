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

namespace Math2

open Finset
open scoped FinsetFamily

/-- **The Kruskal–Katona theorem.**

Let `𝒜` be a family of `r`-element subsets of `Fin n`, and let `𝒞` be a family of `r`-element
subsets which is an initial segment of the colexicographic order (i.e. downwards closed in colex
among `r`-sets) with `#𝒞 ≤ #𝒜`.  Then the shadow of `𝒞` is no larger than the shadow of `𝒜`:
the minimum possible shadow size of a family of `r`-sets is attained by initial segments of
colex. -/
theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜r : ∀ A ∈ 𝒜, #A = r) (h𝒞r : ∀ C ∈ 𝒞, #C = r)
    (h𝒞init : ∀ ⦃C B : Finset (Fin n)⦄, C ∈ 𝒞 →
      (_root_.toColex B : Colex (Finset (Fin n))) < _root_.toColex C → #B = r →
      B ∈ 𝒞)
    (hcard : #𝒞 ≤ #𝒜) :
    #(∂ 𝒞) ≤ #(∂ 𝒜) :=
  Finset.kruskal_katona (fun _ hA ↦ h𝒜r _ hA) hcard
    ⟨fun _ hC ↦ h𝒞r _ hC, fun _ _ hC h ↦ h𝒞init hC h.1 h.2⟩

/-- The Lovász form of the Kruskal–Katona theorem: if `𝒜` is a family of `r`-subsets of `Fin n`
with at least `k.choose r` members (where `i ≤ r ≤ k ≤ n`), then its `i`-th iterated shadow has at
least `k.choose (r - i)` members. -/
theorem kruskal_katona_lovasz_form {n r k i : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) (h𝒜r : ∀ A ∈ 𝒜, #A = r)
    (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) :=
  Finset.kruskal_katona_lovasz_form hir hrk hkn (fun _ hA ↦ h𝒜r _ hA) hcard

end Math2

