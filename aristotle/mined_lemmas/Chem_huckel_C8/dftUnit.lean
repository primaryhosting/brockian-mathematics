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

open Polynomial

/-- A primitive 8-th root of unity. -/

noncomputable def dftUnit : (Matrix (Fin 8) (Fin 8) ℂ)ˣ where
  val := dftMat
  inv := dftInv
  val_inv := dftMat_mul_dftInv
  inv_val := mul_eq_one_comm.mp dftMat_mul_dftInv

