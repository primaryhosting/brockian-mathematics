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

theorem prodLin_modEq {a b N q M : ℕ} (h : b * q ≡ a [MOD M]) :
    prodLin a b N ≡ b ^ N * (Nat.factorial N * Nat.choose (q + N) N) [MOD M] := by
  have h1 : prodLin a b N ≡ ∏ k ∈ Finset.Icc 1 N, (b * (q + k)) [MOD M] := by
    refine prod_modEq fun k _ => ?_
    have hb : b * q + b * k = b * (q + k) := by ring
    rw [← hb]
    exact (h.add_right (b * k)).symm
  have h2 : ∏ k ∈ Finset.Icc 1 N, (b * (q + k)) = b ^ N * ∏ k ∈ Finset.Icc 1 N, (q + k) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]; simp
  have h3 : ∏ k ∈ Finset.Icc 1 N, (q + k) = Nat.factorial N * Nat.choose (q + N) N := by
    rw [prod_Icc_add, Nat.ascFactorial_eq_factorial_mul_choose]
  rw [← h3, ← h2]
  exact h1

