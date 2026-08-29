/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

/-- The family of subsets of `Fin n` corresponding to a family `F` of subsets of `[n]`. -/

private def toFinFamily (n : ℕ) (F : Finset (Finset ℕ)) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter fun s => s.map Fin.valEmbedding ∈ F

