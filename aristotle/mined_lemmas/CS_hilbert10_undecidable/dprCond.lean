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

def dprCond {n m : ℕ} (p : Poly (Fin2 (n + 1) ⊕ Fin m)) (C D : ℕ) (b : Vector3 ℕ n → ℕ)
    (c Y K : ℕ) (v : Vector3 ℕ n) (X : Fin m → ℕ) : Prop :=
  C * (b v + Y + (∑ a, v a) + 1) ^ D + (b v + Y + (∑ a, v a)) < c ∧
  prodLin 1 (Nat.factorial c) (b v) ∣ Nat.factorial c * (K + 1) + 1 ∧
  (∀ j, Y < X j ∧ prodLin 1 (Nat.factorial c) (b v) ∣
      Nat.factorial (Y + 1) * Nat.choose (X j) (Y + 1)) ∧
  prodLin 1 (Nat.factorial c) (b v) ∣ (p (Sum.elim (Vector3.cons K v) X)).natAbs

section

variable {n m : ℕ}

/-- The index type of the variables used in the coding: three scalars `c, Y, K`, the original
variables and the codes `X`. -/
private abbrev Idx (n m : ℕ) : Type := Option (Option (Option (Fin2 n ⊕ Fin m)))

