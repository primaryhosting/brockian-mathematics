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

theorem exists_mul_modEq (a b T : ℕ) : ∃ q, b * q ≡ a [MOD 1 + b * T] := by
  set M := 1 + b * T with hM
  have hcop : Nat.Coprime b M := by
    have hg : Nat.gcd b M = Nat.gcd b 1 := by
      have hc : M = 1 + T * b := by rw [hM]; ring
      rw [hc]
      exact Nat.gcd_add_mul_right_right b 1 T
    simp [Nat.Coprime, hg]
  rcases eq_or_lt_of_le (show 1 ≤ M by omega) with h1 | h1
  · exact ⟨0, by rw [← h1]; exact Nat.modEq_one⟩
  · obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨a * m, ?_⟩
    have hbm : b * m ≡ 1 [MOD M] := by
      unfold Nat.ModEq
      rw [hm, Nat.mod_eq_of_lt h1]
    calc b * (a * m) = a * (b * m) := by ring
      _ ≡ a * 1 [MOD M] := Nat.ModEq.mul_left a hbm
      _ = a := by ring

/-- The Diophantine characterisation of `prodLin`. -/
