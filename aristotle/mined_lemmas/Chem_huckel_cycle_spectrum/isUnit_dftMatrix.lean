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

open Matrix

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/

lemma isUnit_dftMatrix {n : ℕ} (hn : 0 < n) : IsUnit (dftMatrix n) :=
  IsUnit.of_mul_eq_one _ (dft_mul_dftInv hn)

/-! ### The Hückel spectrum of the cycle -/

/-- The columns of the DFT matrix diagonalise the adjacency matrix of the cycle. -/
