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

theorem factorial_diophFn : DiophFn fun v : Vector3 ℕ 1 => Nat.factorial (v &0) := by
  have key : (fun v : Vector3 ℕ 1 => Nat.factorial (v &0))
      = fun v : Vector3 ℕ 1 =>
        (2 ^ (v &0) * (v &0) ^ (v &0 + 2) + 1) ^ (v &0)
          / Nat.choose (2 ^ (v &0) * (v &0) ^ (v &0 + 2) + 1) (v &0) :=
    funext fun v => factorial_eq_div (Nat.lt_succ_self _)
  rw [key]
  have hr : DiophFn fun v : Vector3 ℕ 1 => 2 ^ (v &0) * (v &0) ^ (v &0 + 2) + 1 :=
    (pow_dioph (D.2) (D&0)) D* (pow_dioph (D&0) ((D&0) D+ (D.2))) D+ (D.1)
  exact (pow_dioph hr (D&0)) D/ (choose_dioph hr (D&0))

/-- Diophantine functions are closed under the factorial. -/
