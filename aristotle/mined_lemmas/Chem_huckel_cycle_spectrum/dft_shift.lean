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

lemma dft_shift {n : ℕ} (hn : 0 < n) (a i k : Fin n) (t : ℤ)
    (h : (n : ℤ) ∣ ((a.val : ℤ) - ((i.val : ℤ) + t))) :
    dftMatrix n a k = dftMatrix n i k * ec n (t * k.val) := by
  have h1 : ec n ((a.val : ℤ) * k.val) = ec n (((i.val : ℤ) + t) * k.val) := by
    refine ec_congr hn ?_
    have : (a.val : ℤ) * k.val - ((i.val : ℤ) + t) * k.val
        = ((a.val : ℤ) - ((i.val : ℤ) + t)) * k.val := by ring
    rw [this]
    exact Dvd.dvd.mul_right h _
  have h2 : ((i.val : ℤ) + t) * k.val = (i.val : ℤ) * k.val + t * k.val := by ring
  simp only [dftMatrix]
  rw [h1, h2, ec_add]

/-- Each column of the DFT matrix is an eigenvector of the adjacency matrix of the cycle. -/
