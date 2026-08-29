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

set_option grind.warning false

/-!
## Overview

Langlands reciprocity predicts that (suitable) `n`-dimensional representations of the absolute
Galois group of a global field correspond bijectively to (suitable) automorphic representations
of `GLₙ` over that field, the correspondence being characterized by the requirement that at every
unramified place the Frobenius parameter on the Galois side agrees with the Satake/Hecke parameter
on the automorphic side (equivalently, the two `L`-functions have the same Euler factors).

Since automorphic representations of `GLₙ` are not available in Mathlib, we formalize the *shape*
of a reciprocity law axiomatically (`Frontier.ReciprocityData` and
`Frontier.ReciprocityData.LanglandsReciprocity`): a collection of places, a Galois side, an
automorphic side, and the local parameter attached to an object of either side at a place.  The
conjecture asserts the existence of a parameter-preserving bijection between the two sides.

We then *prove* the base case `n = 1` over `ℚ`, in its classical cyclotomic incarnation
(Artin reciprocity for cyclotomic fields, which by Tate's thesis is exactly the automorphic
reciprocity law for `GL₁/ℚ`):

* the Galois side is the set of one-dimensional complex representations
  `Gal(ℚ(ζ_N)/ℚ) →* ℂˣ` (all Artin representations of dimension one whose conductor divides `N`
  arise this way);
* the automorphic side is the set of Dirichlet characters mod `N`, i.e. via Tate's thesis the
  automorphic representations of `GL₁/ℚ = 𝔸ˣ/ℚˣ` unramified outside `N` and at `∞`;
* the places are the primes `p ∤ N`, i.e. the unramified places;
* the parameter of a Galois character at `p` is its value on the arithmetic Frobenius
  (the Artin symbol) at `p`, and the parameter of a Dirichlet character at `p` is `χ(p)`.

`Frontier.langlands_reciprocity` states that this reciprocity law holds, that the Galois element
used is genuinely the Artin symbol (it raises every `N`-th root of unity to the `p`-th power), and
that consequently every local Euler factor of the Artin `L`-function of `ρ` equals the
corresponding Euler factor of the Dirichlet `L`-function of the matching character.
-/

namespace Frontier

/-- The data entering a reciprocity law: a set of (unramified) places, a "Galois side", an
"automorphic side", and the local parameter attached to an object of each side at each place.

For `GLₙ` one takes for `galoisParam ρ v` (resp. `automorphicParam π v`) a symmetric function of
the Frobenius eigenvalues (resp. of the Satake parameters) of `ρ` (resp. of `π`) at `v`; for
`n = 1` these are just the single Frobenius eigenvalue and the Hecke eigenvalue. -/
structure ReciprocityData where
  /-- The places at which parameters are compared (the unramified places). -/
  Place : Type
  /-- The Galois side of the correspondence. -/
  GaloisSide : Type
  /-- The automorphic side of the correspondence. -/
  AutomorphicSide : Type
  /-- The local (Frobenius) parameter of a Galois object at a place. -/
  galoisParam : GaloisSide → Place → ℂ
  /-- The local (Satake/Hecke) parameter of an automorphic object at a place. -/
  automorphicParam : AutomorphicSide → Place → ℂ

/-- **Langlands reciprocity** for a given collection of data: there is a bijection between the
Galois side and the automorphic side which matches the local parameters at every place.  Matching
of local parameters is exactly the statement that the corresponding `L`-functions agree Euler
factor by Euler factor. -/

theorem artinSymbol_apply (p : UnramifiedPrime N) {x : CyclotomicField N ℚ} (hx : x ^ N = 1) :
    artinSymbol N p x = x ^ (p.1 : ℕ) := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ _ hx, artinSymbol,
    MulEquiv.apply_symm_apply]
  have hval : ((ZMod.unitOfCoprime p.1 p.2.2 : (ZMod N)ˣ) : ZMod N).val = p.1 % N := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [hval]
  conv_rhs => rw [← Nat.div_add_mod p.1 N]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- The bijection between one-dimensional complex representations of `Gal(ℚ(ζ_N)/ℚ)` and Dirichlet
characters mod `N`, induced by the canonical isomorphism `Gal(ℚ(ζ_N)/ℚ) ≃* (ℤ/Nℤ)ˣ`. -/
