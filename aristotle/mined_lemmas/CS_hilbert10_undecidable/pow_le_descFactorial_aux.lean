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

theorem pow_le_descFactorial_aux : ∀ (n r : ℕ), n ≤ r →
    r ^ (n + 1) ≤ r * r.descFactorial n + n * n * r ^ n := by
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have h1 := ih r (by omega)
    have hd : r.descFactorial n ≤ r ^ n := Nat.descFactorial_le_pow r n
    have h2 : r * r.descFactorial n * r ≤ r * r.descFactorial (n + 1) + n * r ^ (n + 1) := by
      rw [Nat.descFactorial_succ]
      have e1 : (r - n) * r.descFactorial n + n * r.descFactorial n = r * r.descFactorial n := by
        rw [← Nat.add_mul]; congr 1; omega
      have hn : n * (r * r.descFactorial n) ≤ n * r ^ (n + 1) := by
        refine Nat.mul_le_mul_left _ ?_
        calc r * r.descFactorial n ≤ r * r ^ n := Nat.mul_le_mul_left _ hd
          _ = r ^ (n + 1) := by ring
      calc r * r.descFactorial n * r
          = r * ((r - n) * r.descFactorial n + n * r.descFactorial n) := by rw [e1]; ring
        _ = r * ((r - n) * r.descFactorial n) + n * (r * r.descFactorial n) := by ring
        _ ≤ r * ((r - n) * r.descFactorial n) + n * r ^ (n + 1) := by omega
    calc r ^ (n + 2) = r ^ (n + 1) * r := by ring
      _ ≤ (r * r.descFactorial n + n * n * r ^ n) * r := Nat.mul_le_mul_right _ h1
      _ = r * r.descFactorial n * r + n * n * r ^ (n + 1) := by ring
      _ ≤ (r * r.descFactorial (n + 1) + n * r ^ (n + 1)) + n * n * r ^ (n + 1) := by omega
      _ ≤ r * r.descFactorial (n + 1) + (n + 1) * (n + 1) * r ^ (n + 1) := by
          nlinarith [Nat.zero_le (r ^ (n + 1))]

/-- A lower bound for the descending factorial. -/
