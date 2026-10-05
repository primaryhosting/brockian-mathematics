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

lemma isBelyiPoly_comp {Q R : ℚ[X]} (hQ : IsBelyiPoly Q) (hR : IsBelyiPoly R)
    (h0 : Q.eval 0 = 0 ∨ Q.eval 0 = 1) (h1 : Q.eval 1 = 0 ∨ Q.eval 1 = 1) :
    IsBelyiPoly (Q.comp R) := by
  refine ⟨?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hQ.1 hR.1
  · intro x hx
    rw [derivative_comp] at hx
    simp only [eval_mul, eval_comp, mul_eq_zero] at hx
    rw [eval_comp]
    rcases hx with hx | hx
    · rcases hR.2 x hx with h | h <;> rw [h]
      · exact h0
      · exact h1
    · exact hQ.2 _ hx

/-! ### The Belyi polynomials -/

