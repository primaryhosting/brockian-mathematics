import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/

lemma circulant_single_mul_single (n : ℕ) [NeZero n] (a b : ZMod n) :
    (Matrix.circulant (Pi.single a 1) : Matrix (ZMod n) (ZMod n) ℂ) *
        Matrix.circulant (Pi.single b 1) =
      Matrix.circulant (Pi.single (a + b) 1) := by
  rw [Matrix.circulant_mul]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  simp only [eq_iff_iff]
  exact sub_eq_iff_eq_add

/-- Powers of the shift matrix are the circulants of the delta functions. -/
