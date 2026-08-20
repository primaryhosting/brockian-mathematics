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

theorem pair_dioph_set : Dioph fun v : Vector3 ℕ 3 => Nat.pair (v &0) (v &1) = v &2 := by
  have h : Dioph fun v : Vector3 ℕ 3 =>
      (v &0 < v &1 ∧ v &2 = v &1 * v &1 + v &0) ∨
        (v &1 ≤ v &0 ∧ v &2 = v &0 * v &0 + v &0 + v &1) :=
    (D&0 D< D&1 D∧ D&2 D= (D&1 D* D&1) D+ D&0) D∨
      (D&1 D≤ D&0 D∧ D&2 D= (D&0 D* D&0) D+ D&0 D+ D&1)
  refine h.ext fun v => ?_
  show ((v &0 < v &1 ∧ v &2 = v &1 * v &1 + v &0) ∨
      (v &1 ≤ v &0 ∧ v &2 = v &0 * v &0 + v &0 + v &1)) ↔ Nat.pair (v &0) (v &1) = v &2
  rw [Nat.pair]
  split_ifs with hlt <;> omega

/-- Cantor pairing is a Diophantine function. -/
