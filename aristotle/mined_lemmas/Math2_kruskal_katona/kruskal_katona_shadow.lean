import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` lines to precede any module doc comment, so the required
header appears immediately after the single `import Mathlib` line.)
-/

open Finset
open scoped FinsetFamily

namespace Math2

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Taking shadows commutes with pushing a family forward along an embedding. -/

theorem kruskal_katona_shadow {r k : ℕ} {𝒜 : Finset (Finset ℕ)} (hr : 1 ≤ r) (hrk : r ≤ k)
    (h𝒜 : (𝒜 : Set (Finset ℕ)).Sized r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - 1) ≤ #(∂ 𝒜) := by
  simpa using kruskal_katona hr hrk h𝒜 hcard

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

