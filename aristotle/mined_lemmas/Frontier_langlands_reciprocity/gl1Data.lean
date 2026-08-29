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

noncomputable def gl1Data : ReciprocityData where
  GaloisRep := GaloisChar n
  AutomorphicRep := DirichletCharacter ℂ n
  galoisCoeff := artinCoeff n
  autCoeff := fun χ m => χ (m : ZMod n)

/-- The reciprocity bijection in the `GL 1` case: a Galois character of `Gal(ℚ(ζₙ)/ℚ)` is
transported along `Gal(ℚ(ζₙ)/ℚ) ≃ (ℤ/nℤ)ˣ` to a Dirichlet character mod `n`. -/
