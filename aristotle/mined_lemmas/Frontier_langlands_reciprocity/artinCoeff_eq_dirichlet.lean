/-
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Polynomial

/-!
## The abstract shape of a reciprocity statement

Langlands reciprocity asserts that Galois representations are matched, bijectively, with
automorphic representations, in such a way that the two sides have the same `L`-function.
Since Mathlib does not (yet) contain automorphic representations of `GL n` over the adeles,
we package the *shape* of such a statement: a type of Galois-side objects, a type of
automorphic-side objects, and, for each, the sequence of Dirichlet coefficients of its
`L`-function.
-/

/-- The data entering a reciprocity statement: a type of Galois representations, a type of
automorphic representations, and the Dirichlet coefficients of the associated `L`-functions. -/
structure ReciprocityData where
  /-- The Galois side: e.g. `n`-dimensional representations of the absolute Galois group. -/
  GaloisRep : Type
  /-- The automorphic side: e.g. cuspidal automorphic representations of `GL n`. -/
  AutomorphicRep : Type
  /-- Dirichlet coefficients of the Artin `L`-function of a Galois representation. -/
  galoisCoeff : GaloisRep → ℕ → ℂ
  /-- Dirichlet coefficients of the automorphic `L`-function. -/
  autCoeff : AutomorphicRep → ℕ → ℂ

/-- **Langlands reciprocity** for a given package of data: there is a bijection between the
Galois side and the automorphic side which preserves `L`-functions, i.e. matches all the
Dirichlet coefficients. -/

theorem artinCoeff_eq_dirichlet (ρ : GaloisChar n) :
    artinCoeff n ρ = fun m : ℕ => (gl1Equiv n ρ) (m : ZMod n) := by
  funext m
  rw [artinCoeff]
  split_ifs with h
  · have hm : ((h.unit : (ZMod n)ˣ) : ZMod n) = (m : ZMod n) := h.unit_spec
    rw [← hm, gl1Equiv]
    simp only [Equiv.trans_apply, MulChar.equivToUnitHom_symm_coe,
      MulEquiv.monoidHomCongrLeftEquiv_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rfl
  · exact ((gl1Equiv n ρ).map_nonunit h).symm

end GL1

/-- **Langlands reciprocity, abelian (`GL 1`) case over `ℚ`.**

For every level `n`, one-dimensional Galois representations of `Gal(ℚ(ζₙ)/ℚ)` are in
bijection with Dirichlet characters mod `n` — the automorphic representations of `GL 1` of
level dividing `n` — in such a way that the Artin `L`-function of a Galois character equals
the Dirichlet `L`-function of the corresponding character, coefficient by coefficient.

This is the base case of the general Langlands reciprocity conjecture, whose shape is
formalized by `Frontier.LanglandsReciprocity`. -/
