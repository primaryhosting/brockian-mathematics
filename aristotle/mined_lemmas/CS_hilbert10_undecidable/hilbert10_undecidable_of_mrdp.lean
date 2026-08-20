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

theorem hilbert10_undecidable_of_mrdp
    (mrdp : ∀ {S : ℕ → Prop}, REPred S → Dioph {v : Fin 1 → ℕ | S (v 0)}) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ =>
        ∃ y : Fin n → ℕ, MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P
          = 0 := by
  obtain ⟨n, p, hp⟩ := dioph_exists_finite_poly (mrdp haltSet_re)
  obtain ⟨P, hP⟩ := exists_mvPolynomial (p.map (Sum.elim (fun _ => (0 : Fin (n + 1))) Fin.succ))
  refine ⟨n, P, fun hcomp => haltSet_not_computable (hcomp.of_eq fun a => ?_)⟩
  have key : ∀ y : Fin n → ℕ,
      MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P
        = p (Sum.elim (fun _ => a) y) := by
    intro y
    rw [hP, Poly.map_apply]
    congr 1
    funext s
    rcases s with i | j <;> simp
  simp only [key]
  exact (hp (fun _ => a)).symm

/-- **Hilbert's tenth problem is undecidable**: there is a polynomial `P` with integer
coefficients in `n + 1` variables such that no algorithm decides, given `a : ℕ`, whether the
equation `P (a, y₁, …, yₙ) = 0` has a solution in natural numbers. -/
