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

theorem poly_finset_support {α β : Type} (p : Poly (α ⊕ β)) :
    ∃ (s : Finset β) (q : Poly (α ⊕ {b // b ∈ s})),
      ∀ (v : α → ℕ) (t : β → ℕ), q (Sum.elim v (fun b => t b.1)) = p (Sum.elim v t) := by
  classical
  induction p using Poly.induction with
  | H1 i =>
    cases i with
    | inl a => exact ⟨∅, Poly.proj (Sum.inl a), fun _ _ => rfl⟩
    | inr b => exact ⟨{b}, Poly.proj (Sum.inr ⟨b, Finset.mem_singleton_self b⟩), fun _ _ => rfl⟩
  | H2 n => exact ⟨∅, Poly.const n, fun _ _ => rfl⟩
  | H3 f g hf hg =>
    obtain ⟨s₁, q₁, h₁⟩ := hf
    obtain ⟨s₂, q₂, h₂⟩ := hg
    refine ⟨s₁ ∪ s₂,
      q₁.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        - q₂.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩)),
      fun v t => ?_⟩
    rw [Poly.sub_apply, Poly.map_apply, Poly.map_apply]
    have e₁ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₁} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    have e₂ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₂} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    rw [e₁, e₂, h₁, h₂]
    rfl
  | H4 f g hf hg =>
    obtain ⟨s₁, q₁, h₁⟩ := hf
    obtain ⟨s₂, q₂, h₂⟩ := hg
    refine ⟨s₁ ∪ s₂,
      q₁.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        * q₂.map (Sum.elim Sum.inl
          (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩)),
      fun v t => ?_⟩
    rw [Poly.mul_apply, Poly.map_apply, Poly.map_apply]
    have e₁ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₁} => Sum.inr ⟨b.1, Finset.mem_union_left _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₁} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    have e₂ : (Sum.elim v (fun b : {b // b ∈ s₁ ∪ s₂} => t b.1)) ∘
        (Sum.elim Sum.inl (fun b : {b // b ∈ s₂} => Sum.inr ⟨b.1, Finset.mem_union_right _ b.2⟩))
        = Sum.elim v (fun b : {b // b ∈ s₂} => t b.1) := by
      funext x; rcases x with a | b <;> rfl
    rw [e₁, e₂, h₁, h₂]
    rfl

/-- Every Diophantine set of tuples can be presented by a polynomial with *finitely many*
auxiliary variables. -/
