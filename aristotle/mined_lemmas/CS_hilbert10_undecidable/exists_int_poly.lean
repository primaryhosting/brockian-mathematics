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

theorem exists_int_poly {n : ℕ} (P₀ : MvPolynomial (Fin (n + 1)) ℤ) :
    ∃ P : MvPolynomial (Fin (n * 4 + 1)) ℤ, ∀ a : ℕ,
      (∃ y : Fin n → ℕ,
          MvPolynomial.eval (fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ)) P₀ = 0)
        ↔ (∃ z : Fin (n * 4) → ℤ, MvPolynomial.eval (Fin.cons (a : ℤ) z) P = 0) := by
  classical
  set sub : Fin (n + 1) → MvPolynomial (Fin (n * 4 + 1)) ℤ :=
    Fin.cases (MvPolynomial.X 0)
      (fun j => ∑ s : Fin 4, (MvPolynomial.X (Fin.succ (finProdFinEquiv (j, s)))) ^ 2) with hsub
  refine ⟨MvPolynomial.bind₁ sub P₀, fun a => ?_⟩
  have hval : ∀ z : Fin (n * 4) → ℤ,
      MvPolynomial.eval (Fin.cons (a : ℤ) z) (MvPolynomial.bind₁ sub P₀)
        = MvPolynomial.eval (fun i => MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub i)) P₀ := by
    intro z; exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _
  have hzero : ∀ z : Fin (n * 4) → ℤ,
      MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub 0) = (a : ℤ) := by
    intro z; simp [hsub]
  have hsucc : ∀ (z : Fin (n * 4) → ℤ) (j : Fin n),
      MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub j.succ)
        = ∑ s : Fin 4, (z (finProdFinEquiv (j, s))) ^ 2 := by
    intro z j; simp [hsub]
  constructor
  · rintro ⟨y, hy⟩
    have hfour : ∀ j : Fin n, ∃ f : Fin 4 → ℕ, ∑ s, (f s) ^ 2 = y j := by
      intro j
      obtain ⟨w, x, u, v, h⟩ := Nat.sum_four_squares (y j)
      exact ⟨![w, x, u, v], by simpa [Fin.sum_univ_four] using h⟩
    choose f hf using hfour
    refine ⟨fun i => ((f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 : ℕ) : ℤ), ?_⟩
    rw [hval]
    rw [show (fun i => MvPolynomial.eval
        (Fin.cons (a : ℤ)
          fun i => ((f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 : ℕ) : ℤ))
        (sub i)) = fun i => ((Fin.cons a y : Fin (n + 1) → ℕ) i : ℤ) from ?_]
    · exact hy
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [hzero]
    · intro j
      rw [hsucc]
      simp only [Equiv.symm_apply_apply, Fin.cons_succ]
      rw [← hf j]
      push_cast
      ring_nf
  · rintro ⟨z, hz⟩
    refine ⟨fun j => (∑ s : Fin 4, (z (finProdFinEquiv (j, s))) ^ 2).toNat, ?_⟩
    rw [hval] at hz
    rw [show (fun i => ((Fin.cons a (fun j => (∑ s : Fin 4, (z (finProdFinEquiv (j, s))) ^ 2).toNat)
        : Fin (n + 1) → ℕ) i : ℤ))
        = fun i => MvPolynomial.eval (Fin.cons (a : ℤ) z) (sub i) from ?_]
    · exact hz
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [hzero]
    · intro j
      rw [hsucc]
      simp only [Fin.cons_succ]
      rw [Int.toNat_of_nonneg (by positivity)]

/-- **Hilbert's tenth problem is undecidable, integer version**: there is a polynomial `P` with
integer coefficients in `m + 1` variables such that no algorithm decides, given `a : ℕ`, whether
the equation `P (a, y₁, …, y_m) = 0` has a solution in integers. -/
