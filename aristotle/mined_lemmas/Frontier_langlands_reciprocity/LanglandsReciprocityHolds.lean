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

/-!
## The abstract shape of Langlands reciprocity

The Langlands reciprocity conjecture asserts that the "Galois side" of arithmetic
(continuous representations of a Galois group) and the "automorphic side"
(automorphic representations of a reductive group) are in a bijection which matches
*local parameters*: at every unramified place `v` the Frobenius conjugacy class on the
Galois side has the same characteristic data as the Satake parameter of the automorphic
representation. Since matching of local parameters at almost all places determines the
matching of the associated `L`-functions, this is the precise content of "reciprocity".

The following predicate isolates that shape, abstracting away the (currently
unformalisable in full) analytic definitions of automorphic representations: a
*reciprocity law* for a pair of local-parameter maps
`galoisParam : 𝒢 → Place → Param` and `autParam : 𝒜 → Place → Param`
is a bijection `𝒢 ≃ 𝒜` matching the parameters at every place.
-/

/-- **Langlands reciprocity, abstract form.** Given a family of "Galois objects" `𝒢`
and "automorphic objects" `𝒜`, each equipped with local parameters at every place of
`Place` valued in `Param`, reciprocity asserts the existence of a bijection between them
which matches the local parameters at all places. -/

def LanglandsReciprocityHolds {𝒢 𝒜 Place Param : Type*}
    (galoisParam : 𝒢 → Place → Param) (autParam : 𝒜 → Place → Param) : Prop :=
  ∃ e : 𝒢 ≃ 𝒜, ∀ ρ : 𝒢, ∀ v : Place, galoisParam ρ v = autParam (e ρ) v

/-!
## The abelian base case: `GL(1)` over `ℚ`

We prove the base case `n = 1` of the conjecture, i.e. reciprocity for `GL(1)`, which is
class field theory for `ℚ` in its cyclotomic (Kronecker–Weber) form.

* Galois side: one-dimensional complex representations, i.e. characters
  `Gal(ℚ(ζ_N)/ℚ) →* ℂˣ`; these are exactly the Artin characters of conductor dividing `N`.
* Automorphic side: automorphic representations of `GL(1)/ℚ` of conductor dividing `N`,
  i.e. Dirichlet characters `DirichletCharacter ℂ N` (Hecke characters of finite order
  and level `N`).
* Places: the primes `p ∤ N`, the places at which both sides are unramified.
* Local parameter: on the Galois side the value `ρ(Frob_p)`, on the automorphic side the
  Satake parameter `χ(p)`.
-/

section GL1

variable (N : ℕ) [NeZero N]

/-- The cyclotomic field `ℚ(ζ_N)`, whose Galois group is the maximal abelian quotient of
`Gal(ℚ̄/ℚ)` of conductor dividing `N`. -/
abbrev CycField : Type := CyclotomicField N ℚ

/-- A one-dimensional (i.e. `GL₁(ℂ)`-valued) Galois representation of conductor dividing
`N`: a character of `Gal(ℚ(ζ_N)/ℚ)`. -/
abbrev GaloisChar : Type := Gal((CycField N)/ℚ) →* ℂˣ

/-- The set of finite places of `ℚ` at which everything in sight is unramified: the primes
not dividing the level `N`. -/
abbrev UnramifiedPlace : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ N}

omit [NeZero N] in
