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

namespace Chem

open Complex Polynomial Matrix

/-- The commutative ring structure on `Fin 20 = ZMod 20`, used for index arithmetic. -/
noncomputable instance : CommRing (Fin 20) := inferInstanceAs (CommRing (ZMod 20))

/-- A primitive 20-th root of unity. -/

lemma sub_one_ne_add_one (i : Fin 20) : i - 1 ≠ i + 1 := by
  intro h
  have h2 : (2 : Fin 20) = 0 := by linear_combination -h
  exact absurd h2 (by decide)

/-- The key computation: the adjacency matrix acts on the Fourier mode `j ↦ ζ(jk)` by the
scalar `2 cos (2πk/20)`. -/
