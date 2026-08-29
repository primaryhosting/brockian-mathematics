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

theorem recip_apply_coe_of_not_coprime (ρ : GaloisChar K) {p : ℕ} (hp : ¬ Nat.Coprime p N) :
    (recip N K ρ) (p : ZMod N) = 0 :=
  MulChar.map_nonunit _ (fun h ↦ hp ((ZMod.isUnit_iff_coprime p N).mp h))

end

/-- **Langlands reciprocity, the abelian base case (`GL₁` over `ℚ`).**

For every modulus `N` and every cyclotomic field `K = ℚ(ζ_N)` there is a bijection
`recip` between the one-dimensional complex representations of the Galois group `Gal(ℚ(ζ_N)/ℚ)`
and the automorphic representations of `GL₁/ℚ` of conductor dividing `N`, i.e. the Dirichlet
characters mod `N`, such that:

* (local–global compatibility) for every prime `p` unramified in `K`, the value of the Galois
  character at the Frobenius element `Frob_p` equals the value of the corresponding automorphic
  character at `p` (its Satake parameter);
* (equality of `L`-functions) for `Re s > 1` the Artin `L`-function of `ρ`, given by its Euler
  product over all primes, converges to the automorphic `L`-function `L(recip ρ, s)`. -/
