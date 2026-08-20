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

theorem nat_prod_dvd_of_coprime {ι : Type*} {s : Finset ι} {f : ι → ℕ} {z : ℕ}
    (hcop : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f)) (hdvd : ∀ i ∈ s, f i ∣ z) :
    (∏ i ∈ s, f i) ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcs : (s : Set ι).Pairwise (Function.onFun Nat.Coprime f) :=
      hcop.mono (by simp [Finset.coe_insert, Set.subset_insert])
    have h1 : f a ∣ z := hdvd a (by simp)
    have h2 : (∏ i ∈ s, f i) ∣ z := ih hcs fun i hi => hdvd i (by simp [hi])
    have h3 : Nat.Coprime (f a) (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2

/-- Gödel's moduli `1 + c ! * k` are pairwise coprime for `1 ≤ k ≤ c`. -/
