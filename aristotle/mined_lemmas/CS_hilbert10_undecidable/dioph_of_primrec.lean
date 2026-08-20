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

theorem dioph_of_primrec {F : ℕ → ℕ} (hF : Nat.Primrec F) :
    DiophFn fun v : Vector3 ℕ 1 => F (v &0) := by
  induction hF with
  | zero => exact D.0
  | succ => exact (D&0) D+ (D.1)
  | left => exact unpair1_diophFn
  | right => exact unpair2_diophFn
  | pair _ _ ihf ihg => exact pairFn_dioph ihf ihg
  | comp _ _ ihf ihg => exact comp1_dioph ihf ihg
  | @prec f g _ _ ihf ihg =>
    refine (diophFn_vec _).2 ?_
    have c1 : Dioph fun w : Vector3 ℕ 3 => Nat.beta (w &0) 0 = f ((w &2).unpair.1) :=
      (beta_dioph (D&0) (D.0)) D= (comp1_dioph ihf (unpair1_dioph (D&2)))
    have c3 : Dioph fun w : Vector3 ℕ 3 => Nat.beta (w &0) ((w &2).unpair.2) = w &1 :=
      (beta_dioph (D&0) (unpair2_dioph (D&2))) D= (D&1)
    have c2 : Dioph fun w : Vector3 ℕ 3 => ∀ i < (w &2).unpair.2,
        Nat.beta (w &0) (i + 1)
          = g (Nat.pair ((w &2).unpair.1) (Nat.pair i (Nat.beta (w &0) i))) := by
      refine bddForall_dioph (R := fun i w => Nat.beta (w &0) (i + 1)
        = g (Nat.pair ((w &2).unpair.1) (Nat.pair i (Nat.beta (w &0) i)))) ?_ (unpair2_dioph (D&2))
      have h : Dioph fun u : Vector3 ℕ 4 => Nat.beta (u &1) (u &0 + 1)
          = g (Nat.pair ((u &3).unpair.1) (Nat.pair (u &0) (Nat.beta (u &1) (u &0)))) :=
        (beta_dioph (D&1) ((D&0) D+ (D.1))) D=
          (comp1_dioph ihg (pairFn_dioph (unpair1_dioph (D&3))
            (pairFn_dioph (D&0) (beta_dioph (D&1) (D&0)))))
      exact h
    refine Dioph.ext ((D∃) 2 (c1 D∧ c2 D∧ c3)) fun v => ?_
    show (∃ c, Nat.beta c 0 = f ((v &1).unpair.1) ∧
        (∀ i < (v &1).unpair.2, Nat.beta c (i + 1)
          = g (Nat.pair ((v &1).unpair.1) (Nat.pair i (Nat.beta c i)))) ∧
        Nat.beta c ((v &1).unpair.2) = v &0) ↔ _
    exact (prec_graph ((v &1).unpair.1) ((v &1).unpair.2) (v &0)).symm

end CS

import RequestProject.Hilbert10.Product

/-!
# Tools for the Davis–Putnam–Robinson theorem

Auxiliary results used in the elimination of bounded universal quantifiers:

* growth and congruence properties of Mathlib's `Poly`;
* the descending factorial as a product;
* divisibility by a product of pairwise coprime numbers;
* coprimality of the Gödel moduli `1 + c ! * k`;
* closure of Diophantine sets under finite conjunctions and of Diophantine functions under
  finite sums.
-/

namespace CS

open Finset Dioph

/-! ## Polynomials -/

/-- Every `Poly` is bounded by `C * (t+1) ^ D` on arguments bounded by `t`. -/
