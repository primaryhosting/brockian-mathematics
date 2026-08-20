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

theorem prodLin_diophFn : DiophFn fun v : Vector3 ℕ 3 => prodLin (v &0) (v &1) (v &2) := by
  refine (diophFn_vec _).2 ?_
  -- variables: `&0` value, `&1` = a, `&2` = b, `&3` = N
  have hM : DiophFn fun v : Vector3 ℕ 4 => 1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3) :=
    (D.1) D+ ((D&2) D* pow_dioph ((D&1) D+ ((D&2) D* (D&3)) D+ (D.1)) (D&3))
  -- after `(D∃) 4`: `&0` = q, `&1` = value, `&2` = a, `&3` = b, `&4` = N
  have hM' : DiophFn fun v : Vector3 ℕ 5 => 1 + v &3 * (v &2 + v &3 * v &4 + 1) ^ (v &4) :=
    (D.1) D+ ((D&3) D* pow_dioph ((D&2) D+ ((D&3) D* (D&4)) D+ (D.1)) (D&4))
  have hinner : Dioph fun v : Vector3 ℕ 5 =>
      (v &3 * v &0 ≡ v &2 [MOD 1 + v &3 * (v &2 + v &3 * v &4 + 1) ^ (v &4)]) ∧
      v &1 = (v &3 ^ (v &4) * (Nat.factorial (v &4) * Nat.choose (v &0 + v &4) (v &4)))
              % (1 + v &3 * (v &2 + v &3 * v &4 + 1) ^ (v &4)) :=
    (Dioph.modEq_dioph ((D&3) D* (D&0)) (D&2) hM') D∧
      ((D&1) D= ((pow_dioph (D&3) (D&4)) D*
        ((factorial_dioph (D&4)) D* (choose_dioph ((D&0) D+ (D&4)) (D&4)))) D% hM')
  have hbig : Dioph fun v : Vector3 ℕ 4 =>
      (v &2 = 0 ∧ v &0 = (v &1) ^ (v &3)) ∨
      (0 < v &2 ∧ ∃ q : ℕ,
        (v &2 * q ≡ v &1 [MOD 1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3)]) ∧
        v &0 = (v &2 ^ (v &3) * (Nat.factorial (v &3) * Nat.choose (q + v &3) (v &3)))
                % (1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3))) :=
    (((D&2) D= (D.0)) D∧ ((D&0) D= pow_dioph (D&1) (D&3))) D∨
      (((D.1) D≤ (D&2)) D∧ ((D∃) 4 hinner))
  refine hbig.ext fun v => ?_
  show ((v &2 = 0 ∧ v &0 = (v &1) ^ (v &3)) ∨
      (0 < v &2 ∧ ∃ q : ℕ,
        (v &2 * q ≡ v &1 [MOD 1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3)]) ∧
        v &0 = (v &2 ^ (v &3) * (Nat.factorial (v &3) * Nat.choose (q + v &3) (v &3)))
                % (1 + v &2 * (v &1 + v &2 * v &3 + 1) ^ (v &3)))) ↔ _
  exact prodLin_iff.symm

section
variable {α : Type} {f g h : (α → ℕ) → ℕ}

/-- Diophantine functions are closed under `prodLin`. -/
