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

lemma isColexInitSeg_iff {𝒞 : Finset (Finset (Fin n))} {r : ℕ} :
    IsColexInitSeg 𝒞 r ↔ Finset.Colex.IsInitSeg 𝒞 r := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun A hA => h₁ A hA, ?_⟩
    rintro A B hA ⟨hlt, hcard⟩
    exact h₂ A hA B (colexLt_iff.2 hlt) hcard
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun A hA => h₁ hA, ?_⟩
    intro A hA B hlt hcard
    exact h₂ hA ⟨colexLt_iff.1 hlt, hcard⟩

/-- **The Kruskal–Katona theorem.** If `𝒜` is a family of `r`-element subsets of `Fin n` and
`𝒞` is an initial segment of the colexicographic order on `r`-sets with `#𝒞 ≤ #𝒜`, then the
shadow of `𝒞` is no larger than the shadow of `𝒜`. In particular, among families of `r`-sets of
a given size, the minimum shadow size is attained by initial segments of the colex order. -/
