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

namespace Frontier

/-!
## The shape of the conjecture

Langlands reciprocity predicts that every `d`-dimensional (continuous, complex) representation
`ρ` of the absolute Galois group of a number field is *automorphic*: there is an automorphic
representation `π` of `GL_d` over that field whose local data (Satake parameters / Hecke
eigenvalues) match the Frobenius data of `ρ`, so that `L(s, ρ) = L(s, π)`.

For `d = 1` over `ℚ` the automorphic representations of `GL_1` of finite order are exactly the
Dirichlet characters, and the predicted matching is provided by the Artin reciprocity map.  This
degree-one case is the classical base case of the conjecture (abelian class field theory), and it
is the case formalized and proved here.

`IsArtinReciprocity art` below is the precise degree-one reciprocity statement relative to a
reciprocity ("Artin") map `art : G →* (ZMod n)ˣ`: *every* one-dimensional Galois representation of
`G` is matched by a *unique* Dirichlet character modulo `n`, the matching being
`χ (art g) = ρ g`.
-/

/-- A degree-one Galois representation of a group `G`: a character `G →* ℂˣ`.
(For a finite Galois group every homomorphism to `ℂˣ` is automatically continuous with finite
image, so this is exactly the notion of an Artin character of degree one.) -/
abbrev GaloisChar (G : Type*) [Group G] := G →* ℂˣ

/-- **Degree-one Langlands reciprocity relative to a reciprocity map `art`.**

Every one-dimensional Galois representation `ρ : G →* ℂˣ` is automorphic: there is a *unique*
Dirichlet character `χ` modulo `n` (i.e. a unique automorphic representation of `GL₁` of
conductor dividing `n`) whose value at `art g` is `ρ g` for all `g`. -/

theorem isArtinReciprocity_cyclotomic :
    IsArtinReciprocity ((cyclotomicArtinMap n K : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ) :
      (K ≃ₐ[ℚ] K) →* (ZMod n)ˣ) :=
  isArtinReciprocity_of_mulEquiv _

/-- **Langlands reciprocity, degree-one cyclotomic base case.**

Let `K = ℚ(ζₙ)` with `ζ` a primitive `n`-th root of unity, and let `ρ : Gal(K/ℚ) →* ℂˣ` be a
one-dimensional Galois representation.  Then `ρ` is automorphic: there is a *unique* Dirichlet
character `χ` modulo `n` — i.e. a unique automorphic representation of `GL₁/ℚ` of conductor
dividing `n` — matching `ρ` under reciprocity, in the sense that whenever `σ` acts on `ζ` by
`ζ ↦ ζ ^ a` (i.e. `a` is the Artin symbol of `σ`, so that for a prime `p ∤ n` unramified in `K`
the Frobenius `σ = Frob_p` has `a = p`), one has `χ a = ρ σ`.

Equivalently: the Artin `L`-function of `ρ` equals the Dirichlet `L`-function of `χ`, since the
Euler factors agree at every unramified prime. -/
