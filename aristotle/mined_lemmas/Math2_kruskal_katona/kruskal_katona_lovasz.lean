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

theorem kruskal_katona_lovasz {r k i : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h𝒜 : ∀ s ∈ 𝒜, #s = r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(shadowIter i 𝒜) := by
  rw [shadowIter_eq]
  exact Finset.kruskal_katona_lovasz_form hir hrk hkn (fun s hs => h𝒜 s hs) hcard

end Math2

#print axioms Math2.kruskal_katona
#print axioms Math2.kruskal_katona_lovasz

