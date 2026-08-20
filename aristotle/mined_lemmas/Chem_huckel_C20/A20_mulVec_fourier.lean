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

lemma A20_mulVec_fourier (k : Fin 20) :
    A20 *ᵥ (fun j : Fin 20 => zeta (j * k)) = ev k • (fun j : Fin 20 => zeta (j * k)) := by
  funext i
  rw [A20, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i)]
  have h1 : (i - 1) * k = i * k + -k := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  rw [h1, h2, zeta_add, zeta_add, Pi.smul_apply, smul_eq_mul, ← ev_eq]
  ring

