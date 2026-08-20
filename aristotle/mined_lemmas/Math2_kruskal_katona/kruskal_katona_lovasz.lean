/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
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
open Finset.Colex

variable {n : ℕ}

/-- The (lower) shadow of a family of finite sets: all sets obtained from a member of the
family by deleting a single element. -/

theorem kruskal_katona_lovasz {r k i : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) (h𝒜 : ∀ A ∈ 𝒜, A.card = r)
    (hcard : k.choose r ≤ 𝒜.card) :
    k.choose (r - i) ≤ (shadow^[i] 𝒜).card := by
  have hfun : (shadow : Finset (Finset (Fin n)) → Finset (Finset (Fin n))) = Finset.shadow :=
    funext shadow_eq
  rw [hfun]
  exact Finset.kruskal_katona_lovasz_form hir hrk hkn (fun A hA => h𝒜 A hA) hcard

end Math2

