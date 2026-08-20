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

def ColexLt (A B : Finset (Fin n)) : Prop :=
  ∃ a ∈ B, a ∉ A ∧ ∀ b ∈ A, b ∉ B → b < a

/-- `𝒞` is an initial segment of the colexicographic order on `r`-sets: all its members have
size `r`, and any `r`-set below a member of `𝒞` in colex is again in `𝒞`. -/
