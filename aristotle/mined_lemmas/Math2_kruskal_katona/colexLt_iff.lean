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

lemma colexLt_iff {s t : Finset (Fin n)} :
    ColexLt s t ↔ toColex s < toColex t :=
  Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt.symm

/-- **The Kruskal–Katona theorem.**

Let `𝒜` be a family of `r`-element subsets of `Fin n`, and let `𝒞` be an initial segment of the
colexicographic order on `r`-element sets (that is, `𝒞` consists of `r`-sets and is downwards
closed in colex among `r`-sets) with `#𝒞 ≤ #𝒜`. Then the shadow of `𝒞` is no larger than the
shadow of `𝒜`; in other words, among families of `r`-sets of a given size, the initial segments
of colex minimise the size of the shadow. -/
