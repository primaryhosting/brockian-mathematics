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

lemma exists_repr_of_mem_Ioo {l : ℚ} (h0 : 0 < l) (h1 : l < 1) :
    ∃ m n : ℕ, l = (m + 1 : ℚ) / (m + n + 2) := by
  set p : ℕ := l.num.toNat with hp
  have hnum : (0 : ℤ) < l.num := Rat.num_pos.mpr h0
  have hpnum : (p : ℤ) = l.num := Int.toNat_of_nonneg hnum.le
  have hplt : p < l.den := by
    have hden : (0 : ℚ) < (l.den : ℚ) := by exact_mod_cast l.pos
    have hkey : (l.num : ℚ) = l * (l.den : ℚ) := (Rat.mul_den_eq_num l).symm
    have hlt : (l.num : ℚ) < (l.den : ℚ) := by rw [hkey]; nlinarith
    have : l.num < (l.den : ℤ) := by exact_mod_cast hlt
    omega
  have hppos : 0 < p := by omega
  refine ⟨p - 1, l.den - p - 1, ?_⟩
  have e1 : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by
    have key : (p - 1) + 1 = p := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) key
  have e2 : ((p - 1 : ℕ) : ℚ) + ((l.den - p - 1 : ℕ) : ℚ) + 2 = (l.den : ℚ) := by
    have key : (p - 1) + (l.den - p - 1) + 2 = l.den := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) key
  rw [e1, e2]
  rw [show ((p : ℚ)) = ((l.num : ℚ)) by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hpnum]
  exact (Rat.num_div_den l).symm

/-- **Belyi reduction over `ℚ`.**  For every finite set `S` of rational numbers there is a Belyi
polynomial mapping `S` into `{0, 1}`. -/
