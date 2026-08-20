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

theorem unpair1_diophFn : DiophFn fun v : Vector3 ℕ 1 => (v &0).unpair.1 := by
  refine (diophFn_vec _).2 ?_
  have h : Dioph fun v : Vector3 ℕ 2 => ∃ b : ℕ, Nat.pair (v &0) b = v &1 :=
    Dioph.ext ((D∃) 2 (dioph_comp pair_dioph_set
      [fun w : Vector3 ℕ 3 => w &1, fun w => w &0, fun w => w &2] ⟨D&1, D&0, D&2⟩))
      fun _ => Iff.rfl
  refine h.ext fun v => ?_
  show (∃ b : ℕ, Nat.pair (v &0) b = v &1) ↔ (v &1).unpair.1 = v &0
  constructor
  · rintro ⟨b, hb⟩; rw [← hb, Nat.unpair_pair]
  · intro h; exact ⟨(v &1).unpair.2, by rw [← h, Nat.pair_unpair]⟩

/-- The second component of unpairing is a Diophantine function. -/
