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

theorem bddForall_dioph {n : ℕ} {R : ℕ → Vector3 ℕ n → Prop}
    (dR : Dioph fun u : Vector3 ℕ (n + 1) => R (u &0) (u ∘ fs))
    {b : Vector3 ℕ n → ℕ} (db : DiophFn b) :
    Dioph fun v : Vector3 ℕ n => ∀ i < b v, R i v := by
  classical
  obtain ⟨m, p, hp⟩ := dioph_exists_finite_poly dR
  obtain ⟨C, D, hCD⟩ := poly_bound p
  have hR : ∀ (i : ℕ) (v : Vector3 ℕ n),
      R i v ↔ ∃ t : Fin m → ℕ, p (Sum.elim (Vector3.cons i v) t) = 0 := by
    intro i v
    have h := hp (Vector3.cons i v)
    have e2 : (Vector3.cons i v) ∘ fs = v := funext fun j => rfl
    have e3 : R ((Vector3.cons i v) &0) ((Vector3.cons i v) ∘ fs) ↔ R i v := by
      rw [e2]; exact Iff.rfl
    exact e3.symm.trans h
  have step := ex_dioph (ex1_dioph (ex1_dioph (ex1_dioph (dprCond_dioph p C D db))))
  refine step.ext fun v => ?_
  constructor
  · rintro ⟨X, K, Y, c, hcond⟩
    have hcond' : dprCond p C D b c Y K v X := hcond
    intro i hi
    rw [hR i v]
    refine (dpr_core p C D hCD v (∑ a, v a) (fun a => Finset.single_le_sum
      (f := fun a : Fin2 n => v a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (b v)).2
      ⟨c, Y, K, X, hcond'.1, hcond'.2.1, hcond'.2.2.1, hcond'.2.2.2⟩ i hi
  · intro h
    have h' : ∀ i < b v, ∃ t : Fin m → ℕ, p (Sum.elim (Vector3.cons i v) t) = 0 := by
      intro i hi
      exact (hR i v).1 (h i hi)
    obtain ⟨c, Y, K, X, h1, h2, h3, h4⟩ :=
      (dpr_core p C D hCD v (∑ a, v a) (fun a => Finset.single_le_sum
        (f := fun a : Fin2 n => v a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (b v)).1 h'
    exact ⟨X, K, Y, c, ⟨h1, h2, h3, h4⟩⟩

end CS

import RequestProject.Hilbert10.DiophTools

/-!
# Binomial coefficients and factorials are Diophantine

Given that exponentiation is Diophantine (Matiyasevich's theorem, `Dioph.pow_dioph` in Mathlib),
binomial coefficients and factorials are Diophantine as well, by two classical formulas of
Julia Robinson:

* `Nat.choose n k` is the `k`-th digit of `(u+1)^n` written in base `u`, as soon as `u > 2^n`;
* `Nat.factorial n = r ^ n / Nat.choose r n` as soon as `r` is large enough compared with `n`.
-/

namespace CS

open Finset

/-! ## Digit extraction -/

/-- Reading off a digit of a number given by its base-`u` expansion. -/
