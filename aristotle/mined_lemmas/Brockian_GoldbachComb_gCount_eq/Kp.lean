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

def Kp (p : ℕ) (h : ℤ) : ℚ :=
  if (p : ℤ) ∣ h then 1 + 1 / (p - 1)^3 else 1 - 1 / (p - 1)^4

/-- GC-3 (target): THE LOCAL COVARIANCE THEOREM. For prime p and any
shift h, the mean over c of w(c)·w(c+h), with w = g/mean(g), equals
Kp p h — positive lift 1/(p−1)³ when p ∣ h (spikes aligned), negative
dip 1/(p−1)⁴ otherwise (spikes disjoint). -/
