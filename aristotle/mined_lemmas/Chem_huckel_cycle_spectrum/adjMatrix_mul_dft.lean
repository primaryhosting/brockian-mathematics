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

lemma adjMatrix_mul_dft {m : ℕ} (hm : 1 ≤ m) (i k : Fin (m + 2)) :
    ((SimpleGraph.cycleGraph (m + 2)).adjMatrix ℂ * dftMatrix (m + 2)) i k
      = (huckelEnergy (m + 2) k.val : ℂ) * dftMatrix (m + 2) i k := by
  have hn : 0 < m + 2 := by omega
  have h1 : (((1 : Fin (m + 2)) : ℕ) : ℤ) = 1 := by
    exact_mod_cast fin_val_one (n := m + 2) (by omega)
  have hne : i - 1 ≠ i + 1 := cycle_neighbors_ne (n := m + 2) (by omega) i
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair hne]
  have hplus : dftMatrix (m + 2) (i + 1) k = dftMatrix (m + 2) i k * ec (m + 2) (1 * k.val) := by
    refine dft_shift hn _ _ _ 1 ?_
    have := fin_val_add_cong i 1
    rwa [h1] at this
  have hminus : dftMatrix (m + 2) (i - 1) k
      = dftMatrix (m + 2) i k * ec (m + 2) ((-1 : ℤ) * k.val) := by
    refine dft_shift hn _ _ _ (-1) ?_
    have := fin_val_sub_cong i 1
    rw [h1] at this
    have heq : ((i.val : ℤ) - 1) = ((i.val : ℤ) + (-1)) := by ring
    rwa [heq] at this
  rw [hplus, hminus, ← mul_add]
  have : ec (m + 2) ((-1 : ℤ) * k.val) + ec (m + 2) (1 * k.val)
      = (huckelEnergy (m + 2) k.val : ℂ) := by
    rw [show ((-1 : ℤ) * k.val) = -(k.val : ℤ) by ring, show ((1 : ℤ) * k.val) = (k.val : ℤ) by ring,
      add_comm]
    exact ec_add_neg (m + 2) k.val
  rw [this, mul_comm]

/-! ### Invertibility of the DFT matrix -/

/-- The inverse of the (unnormalised) DFT matrix. -/
