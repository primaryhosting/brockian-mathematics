/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Hilbert10.Basic
import RequestProject.Hilbert10.MRDP

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

The development is organised as follows.

* `RequestProject.Hilbert10.Basic`: the halting set is r.e. but not computable, normalisation of
  Diophantine sets, and the passage from Mathlib's `Poly` to `MvPolynomial`.
* `RequestProject.Hilbert10.DiophTools`: pairing, unpairing and Gödel's `β` function are
  Diophantine.
* `RequestProject.Hilbert10.Choose`, `.Product`: binomial coefficients, factorials and products
  of arithmetic progressions are Diophantine.
* `RequestProject.Hilbert10.DPRTools`, `.DPRCore`, `.BddForall`: the Davis–Putnam–Robinson
  theorem, i.e. Diophantine relations are closed under bounded universal quantification.
* `RequestProject.Hilbert10.Primrec`: primitive recursive functions have Diophantine graphs.
* `RequestProject.Hilbert10.MRDP`: the MRDP theorem, every r.e. set of naturals is Diophantine.

This file combines these into the undecidability of Hilbert's tenth problem, over `ℕ`
(`CS.hilbert10_undecidable`) and over `ℤ` (`CS.hilbert10_undecidable_int`).
-/

namespace CS

/-- The reduction of Hilbert's tenth problem to the MRDP theorem: if every r.e. set of naturals
is Diophantine, then no algorithm decides solvability of a suitable Diophantine equation with a
natural number parameter.  (This implication is proved unconditionally; the MRDP hypothesis is
supplied by `CS.dioph_of_rePred`.) -/

theorem moduli_coprime_lt {c k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hlc : l ≤ c) :
    Nat.Coprime (1 + Nat.factorial c * k) (1 + Nat.factorial c * l) := by
  set d := Nat.factorial c with hd
  by_contra hcop
  obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd hcop
  have h1 : q ∣ 1 + d * k := hdvd.trans (Nat.gcd_dvd_left _ _)
  have h2 : q ∣ 1 + d * l := hdvd.trans (Nat.gcd_dvd_right _ _)
  have hqd : ¬ (q ∣ d) := by
    intro h
    have h4 : q ∣ (1 + d * k) - d * k := Nat.dvd_sub h1 (h.mul_right k)
    simp at h4
    exact hq.one_lt.ne' h4
  have h3 : q ∣ d * (l - k) := by
    have h5 := Nat.dvd_sub h2 h1
    have h6 : (1 + d * l) - (1 + d * k) = d * (l - k) := by rw [Nat.mul_sub]; omega
    rwa [h6] at h5
  rcases (Nat.Prime.dvd_mul hq).1 h3 with h | h
  · exact hqd h
  · have hle : q ≤ l - k := Nat.le_of_dvd (by omega) h
    exact hqd (Nat.dvd_factorial hq.pos (by omega))

/-- Symmetric version of `moduli_coprime_lt`. -/
