/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

namespace Chem

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma dft_inversion (v : Fin 15 → ℂ) (j : Fin 15) :
    ∑ k : Fin 15, chi ((k : ℕ) : ℤ) j * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i)
      = 15 * v j := by
  have step : ∀ k i : Fin 15,
      chi ((k : ℕ) : ℤ) j * (chi (-((k : ℕ) : ℤ)) i * v i)
        = chi (((j : ℕ) : ℤ) - (i : ℕ)) k * v i := by
    intro k i
    rw [chi, chi, chi, ← mul_assoc, ← W_add]
    congr 2
    ring
  calc ∑ k : Fin 15, chi ((k : ℕ) : ℤ) j * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i)
      = ∑ k : Fin 15, ∑ i : Fin 15, chi (((j : ℕ) : ℤ) - (i : ℕ)) k * v i := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => step k i)
    _ = ∑ i : Fin 15, (∑ k : Fin 15, chi (((j : ℕ) : ℤ) - (i : ℕ)) k) * v i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
    _ = 15 * v j := by
        rw [Finset.sum_eq_single j]
        · rw [char_sum]
          simp
        · intro i _ hij
          rw [char_sum]
          have h1 : (i : ℕ) < 15 := i.isLt
          have h2 : (j : ℕ) < 15 := j.isLt
          have h3 : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
          have : ¬ (15 : ℤ) ∣ (((j : ℕ) : ℤ) - (i : ℕ)) := by omega
          simp [this]
        · intro h
          exact absurd (Finset.mem_univ j) h

/-- The Fourier coefficients diagonalise the eigenvalue equation. -/
