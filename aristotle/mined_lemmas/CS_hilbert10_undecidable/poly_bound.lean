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

theorem poly_bound {α : Type} (p : Poly α) :
    ∃ C D : ℕ, ∀ (u : α → ℕ) (t : ℕ), (∀ i, u i ≤ t) → (p u).natAbs ≤ C * (t + 1) ^ D := by
  induction p using Poly.induction with
  | H1 i =>
    refine ⟨1, 1, fun u t ht => ?_⟩
    simp only [Poly.proj_apply]
    calc (u i : ℤ).natAbs = u i := by simp
      _ ≤ t := ht i
      _ ≤ 1 * (t + 1) ^ 1 := by simp
  | H2 n => exact ⟨n.natAbs, 0, fun u t _ => by simp [Poly.const_apply]⟩
  | H3 f g hf hg =>
    obtain ⟨C₁, D₁, h₁⟩ := hf
    obtain ⟨C₂, D₂, h₂⟩ := hg
    refine ⟨C₁ + C₂, max D₁ D₂, fun u t ht => ?_⟩
    have e1 := h₁ u t ht
    have e2 := h₂ u t ht
    have hle1 : C₁ * (t + 1) ^ D₁ ≤ C₁ * (t + 1) ^ (max D₁ D₂) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have hle2 : C₂ * (t + 1) ^ D₂ ≤ C₂ * (t + 1) ^ (max D₁ D₂) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    calc ((f - g) u).natAbs ≤ (f u).natAbs + (g u).natAbs := by
          rw [Poly.sub_apply]; exact Int.natAbs_sub_le _ _
      _ ≤ C₁ * (t + 1) ^ (max D₁ D₂) + C₂ * (t + 1) ^ (max D₁ D₂) := by omega
      _ = (C₁ + C₂) * (t + 1) ^ (max D₁ D₂) := by ring
  | H4 f g hf hg =>
    obtain ⟨C₁, D₁, h₁⟩ := hf
    obtain ⟨C₂, D₂, h₂⟩ := hg
    refine ⟨C₁ * C₂, D₁ + D₂, fun u t ht => ?_⟩
    rw [Poly.mul_apply, Int.natAbs_mul]
    calc (f u).natAbs * (g u).natAbs ≤ (C₁ * (t + 1) ^ D₁) * (C₂ * (t + 1) ^ D₂) :=
          Nat.mul_le_mul (h₁ u t ht) (h₂ u t ht)
      _ = C₁ * C₂ * (t + 1) ^ (D₁ + D₂) := by ring

/-- Polynomials respect congruences. -/
