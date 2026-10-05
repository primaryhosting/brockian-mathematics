/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalised here

Belyi's theorem says that a smooth projective curve is defined over `ℚ̄` if and only if it admits
a map to `ℙ¹` ramified only over `{0, 1, ∞}`.  The substantial half of Belyi's proof is the
*Belyi reduction*: an explicit algorithm which, starting from a map whose branch locus is a finite
set of algebraic points, composes it with suitable polynomials until the branch locus is contained
in `{0, 1, ∞}`.

This file formalises that algorithm over `ℚ`, in the self-contained form of an equivalence
(the statement `Math2.belyi_theorem`):

> a set `S ⊆ ℚ` is finite **iff** there is a non-constant `P ∈ ℚ[X]` which maps `S` into `{0,1}`
> and all of whose finite critical values lie in `{0,1}`.

Viewed as a self-map of `ℙ¹`, such a `P` is unramified outside `{0, 1, ∞}` (a polynomial is
totally ramified over `∞`), i.e. it *is* a Belyi map for `ℙ¹` which moreover kills the prescribed
set `S` of marked points.  The forward direction is the Belyi reduction algorithm (normalise `S`
by an affine map, then repeatedly compose with the Belyi polynomials
`c · x^m (1-x)^n`, each step lowering the number of bad values); the backward direction says that
only finitely many points can be marked this way, since `P⁻¹{0,1}` is finite.
-/

open Polynomial

namespace Math2

/-- A polynomial `P ∈ ℚ[X]` is a *Belyi polynomial* if it is non-constant and all of its finite
critical values lie in `{0, 1}`.  Viewed as a map `ℙ¹ → ℙ¹`, such a `P` is unramified outside
`{0, 1, ∞}`, the point `∞` being totally ramified for every polynomial. -/

theorem belyi_theorem (S : Set ℚ) :
    S.Finite ↔ ∃ P : ℚ[X], IsBelyiPoly P ∧ ∀ s ∈ S, P.eval s = 0 ∨ P.eval s = 1 := by
  constructor
  · intro hS
    obtain ⟨P, hP, hPval⟩ := exists_isBelyiPoly hS.toFinset
    exact ⟨P, hP, fun s hs => hPval s (by simpa using hs)⟩
  · rintro ⟨P, hP, hPval⟩
    have hP0 : P ≠ 0 := by
      intro h
      have hd := hP.1
      rw [h] at hd
      simp at hd
    have hP1 : P - 1 ≠ 0 := by
      intro h
      have hd := hP.1
      have hPeq : P = 1 := by linear_combination (norm := ring_nf) h
      rw [hPeq] at hd
      simp at hd
    have hfin : ({x : ℚ | P.IsRoot x} ∪ {x : ℚ | (P - 1).IsRoot x}).Finite :=
      (Polynomial.finite_setOf_isRoot hP0).union (Polynomial.finite_setOf_isRoot hP1)
    refine hfin.subset ?_
    intro s hs
    rcases hPval s hs with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show (P - 1).IsRoot s
      simp [IsRoot.def, h]

end Math2

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

