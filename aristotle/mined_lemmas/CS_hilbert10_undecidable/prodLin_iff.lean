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

theorem prodLin_iff {a b N z : ℕ} :
    prodLin a b N = z ↔
      (b = 0 ∧ z = a ^ N) ∨
      (0 < b ∧ ∃ q, b * q ≡ a [MOD 1 + b * (a + b * N + 1) ^ N] ∧
        z = (b ^ N * (Nat.factorial N * Nat.choose (q + N) N))
              % (1 + b * (a + b * N + 1) ^ N)) := by
  have main : ∀ q : ℕ, 0 < b → b * q ≡ a [MOD 1 + b * (a + b * N + 1) ^ N] →
      prodLin a b N = (b ^ N * (Nat.factorial N * Nat.choose (q + N) N))
        % (1 + b * (a + b * N + 1) ^ N) := by
    intro q hb hq
    have h := prodLin_modEq (N := N) (M := 1 + b * (a + b * N + 1) ^ N) hq
    calc prodLin a b N = prodLin a b N % (1 + b * (a + b * N + 1) ^ N) :=
          (Nat.mod_eq_of_lt (prodLin_lt hb)).symm
      _ = _ := h
  constructor
  · rintro rfl
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Or.inl ⟨rfl, prodLin_zero a N⟩
    · obtain ⟨q, hq⟩ := exists_mul_modEq a b ((a + b * N + 1) ^ N)
      exact Or.inr ⟨hb, q, hq, main q hb hq⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hb, q, hq, rfl⟩)
    · exact prodLin_zero a N
    · exact main q hb hq

/-! ## Diophantine description -/

section Dioph

open Dioph Fin2 Vector3

/-- The product `∏_{k=1}^{N} (a + b k)` is a Diophantine function of `(a, b, N)`. -/
