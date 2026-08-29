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

set_option grind.warning false

open Polynomial IsCyclotomicExtension

namespace Frontier

/-!
## The shape of a reciprocity law

Langlands reciprocity asserts that the *Galois side* of arithmetic (Galois representations,
with their local Frobenius data at unramified places) and the *automorphic side*
(automorphic representations, with their local Satake/Hecke data) are in a bijection that
matches the local data place by place.  The structure `ReciprocityLaw` below records exactly
this shape: a bijection between the two collections of objects, together with the
local-data maps and the requirement that they agree under the bijection.  A reciprocity law
in this sense immediately gives equality of all the local Euler factors, hence of the
associated `L`-functions.

## What is proved here

We prove the abelian base case: **the `GL(1)` case of Langlands reciprocity over `ℚ`**, i.e.
class field theory for the cyclotomic extensions of `ℚ`.  The automorphic side consists of
the Dirichlet characters mod `N` (the automorphic representations of `GL(1)/ℚ` of conductor
dividing `N`), the Galois side of the (necessarily continuous, finite-image) characters of
`Gal(ℚ(ζ_N)/ℚ)`, and for a prime `p ∤ N` the local datum is the value at the Frobenius
element `Frob_p`, which is the unique automorphism with `ζ ↦ ζ ^ p`.  The reciprocity
statement is that under the correspondence, `ρ(Frob_p) = χ(p)` for all such `p`, so that all
unramified Euler factors — hence the Artin `L`-function of `ρ` and the Dirichlet `L`-function
of `χ` — agree.
-/

/-- The abstract shape of a *reciprocity law*: a bijection between automorphic objects and
Galois objects which matches the local data attached to each object at every place. -/
structure ReciprocityLaw (GalRep AutRep Place LocalData : Type*) where
  /-- The correspondence: automorphic objects ↔ Galois objects. -/
  correspondence : AutRep ≃ GalRep
  /-- Local data on the Galois side (Frobenius conjugacy data at a place). -/
  galLocalData : GalRep → Place → LocalData
  /-- Local data on the automorphic side (Satake / Hecke data at a place). -/
  autLocalData : AutRep → Place → LocalData
  /-- The two local data agree under the correspondence. -/
  local_compat : ∀ (π : AutRep) (v : Place), galLocalData (correspondence π) v = autLocalData π v

/-!
## Auxiliary lemmas
-/


lemma gl1Correspondence_apply (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) :
    ((gl1Correspondence N χ σ : ℂˣ) : ℂ) = χ ((cycGalEquiv N σ : (ZMod N)ˣ) : ZMod N) := by
  simp [gl1Correspondence, MulChar.coe_n]

/-!
## Langlands reciprocity for `GL(1)` over `ℚ`
-/

/-- **Langlands reciprocity, the `GL(1)` case over `ℚ` (abelian class field theory for
cyclotomic fields).**

For every level `N ≥ 1` there is a bijection `Φ` between the automorphic side — the
Dirichlet characters mod `N`, i.e. the automorphic representations of `GL(1)/ℚ` whose
conductor divides `N` — and the Galois side — the characters of `Gal(ℚ(ζ_N)/ℚ)` — such
that for every prime `p` unramified in `ℚ(ζ_N)/ℚ` (equivalently `p ∤ N`):

* the Frobenius element at `p` exists, namely a `ℚ`-automorphism `σ` of `ℚ(ζ_N)` with
  `σ ζ = ζ ^ p`; and
* for every such `σ` and every Dirichlet character `χ`, the Galois local datum
  `Φ χ (Frob_p)` equals the automorphic local datum `χ(p)`.

Thus the correspondence matches the local (Satake / Frobenius) parameters at every
unramified place, which is precisely the reciprocity assertion in this case; equality of
all Euler factors follows (see `Frontier.langlands_reciprocity_euler_factor`). -/
