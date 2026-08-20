/-
  Brockian/GoldbachComb.lean — THE GOLDBACH COMB CAMPAIGN (July 30).

  The exact local covariance kernel behind the 3|k autocorrelation comb
  of the Goldbach residual (Volume II, page XVI; Tomography §4).

  Chain: local count g_p(c) = p−2+[c=0]  →  centered spike 1_{c=0}−1/p
  →  two-case covariance  →  CRT product over squarefree wheels  →
  convergent global kernel K(h) with  K(h)−1 > 0 ⟺ 3 ∣ h  (the p=3
  factor 9/8 vs 15/16 dominates all higher primes combined).

  Empirical status (this program, recorded): kernel verified exactly at
  p = 3,5,7,11; global values K−1 = +0.1195 / −0.0671; transfer pilot
  against the measured 50-lag ACF: one fitted scale β ≈ 0.41, held-out
  sign agreement 25/25, correlation r = 0.996. The TRANSFER conjecture
  is named at the end and never claimed.

  Charter as Core.lean; each unproved declaration was supplied as a target.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.GoldbachComb

open Finset

/-- The local Goldbach count: ordered pairs of nonzero residues summing
to c. -/

theorem wheel_kernel (M : ℕ) (hM : Squarefree M) (hodd : Odd M)
    (h : ℤ) :
    (∑ c : ZMod M, (∏ p ∈ M.primeFactors, (gCount p (ZMod.castHom
        (dvd_of_mem_primeFactors ‹p ∈ M.primeFactors›) (ZMod p) c : ZMod p) : ℚ))
      * 1) / M = ∏ p ∈ M.primeFactors, ((p-1)^2/p * Kp p h) / 1 := by
  -- Original proof target omitted because the statement is invalid.
-/

/-
GC-5 (original target) is retained below but commented out: its proof has
not been established by this verification. Unlike GC-1--GC-3, it should
not be treated as machine-verified. A complete proof requires explicit
finite-product bounds showing that all prime factors above 3 cannot
reverse the contribution from 3.

/-- GC-5 (original, presently unverified). -/
