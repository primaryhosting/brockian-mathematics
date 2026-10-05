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

namespace Frontier

open Complex IsCyclotomicExtension

/-! ## Setting

Langlands reciprocity predicts a bijection between `n`-dimensional complex representations of
the absolute Galois group of a number field and automorphic representations of `GLₙ`, matching
Artin `L`-functions with automorphic `L`-functions, and matching, at each unramified place, the
Frobenius conjugacy class with the Satake parameter of the local component.

We formalise and *prove* the abelian base case `n = 1` over `ℚ`, in its cyclotomic incarnation:
one-dimensional complex representations of `Gal(ℚ(ζ_N)/ℚ)` correspond bijectively to automorphic
representations of `GL₁/ℚ` of conductor dividing `N`, i.e. to Dirichlet characters mod `N`,
in a way which is compatible with Frobenius elements at all unramified primes and which
identifies the Artin `L`-function with the automorphic (Dirichlet) `L`-function.
-/

section

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {N} ℚ K]

/-- A one-dimensional complex representation of the Galois group `Gal(ℚ(ζ_N)/ℚ)`
(the "Galois side" of the correspondence in the abelian case). -/
abbrev GaloisChar : Type _ := (K ≃ₐ[ℚ] K) →* ℂˣ

/-- The (arithmetic) Frobenius at an unramified prime `p`, i.e. a prime not dividing `N`:
it is the unique element of `Gal(ℚ(ζ_N)/ℚ)` acting on `N`-th roots of unity by `ζ ↦ ζ ^ p`. -/

noncomputable def artinEulerFactor (ρ : GaloisChar K) (p : ℕ) (s : ℂ) : ℂ :=
  if h : Nat.Coprime p N then (1 - (ρ (frob N K h) : ℂ) * (p : ℂ) ^ (-s))⁻¹ else 1

/-- The reciprocity map itself: a Galois character `ρ` of `Gal(ℚ(ζ_N)/ℚ)` is transported, along
the cyclotomic isomorphism `Gal(ℚ(ζ_N)/ℚ) ≃* (ℤ/Nℤ)ˣ` of class field theory, to a Dirichlet
character mod `N` (= an automorphic representation of `GL₁/ℚ` of conductor dividing `N`). -/
