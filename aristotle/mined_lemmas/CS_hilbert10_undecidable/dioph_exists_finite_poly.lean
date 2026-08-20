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

theorem dioph_exists_finite_poly {α : Type} {S : Set (α → ℕ)} (h : Dioph S) :
    ∃ (n : ℕ) (p : Poly (α ⊕ Fin n)), ∀ v, v ∈ S ↔ ∃ t : Fin n → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p, hp⟩ := h
  obtain ⟨s, q, hq⟩ := poly_finset_support p
  set e := Fintype.equivFin {b // b ∈ s} with he
  refine ⟨Fintype.card {b // b ∈ s},
    q.map (Sum.elim Sum.inl (fun b : {b // b ∈ s} => Sum.inr (e b))), fun v => ?_⟩
  have key : ∀ u : Fin (Fintype.card {b // b ∈ s}) → ℕ,
      (q.map (Sum.elim Sum.inl (fun b : {b // b ∈ s} => Sum.inr (e b)))) (Sum.elim v u)
        = q (Sum.elim v (fun b => u (e b))) := by
    intro u
    rw [Poly.map_apply]
    congr 1
    funext x; rcases x with a | b <;> rfl
  refine Iff.trans (hp v) ?_
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j => t (e.symm j).1, ?_⟩
    rw [key]
    simpa using (hq v t).trans ht
  · rintro ⟨u, hu⟩
    refine ⟨fun b => if h : b ∈ s then u (e ⟨b, h⟩) else 0, ?_⟩
    rw [← hq v]
    rw [key] at hu
    simpa using hu

/-- Mathlib's `Poly` functions are exactly the evaluations of multivariate integer polynomials. -/
