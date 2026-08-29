/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.structureInstances true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The tilt construction

For a field (more generally, a commutative monoid) `K` and a prime `p`, Scholze's *tilt*
`K♭` is, as a multiplicative monoid, the inverse limit

  `K♭ = lim (⋯ → K --x ↦ xᵖ--> K --x ↦ xᵖ--> K)`,

realised here as the submonoid of sequences `f : ℕ → K` with `f (n+1) ^ p = f n`.
This description of the underlying multiplicative monoid is characteristic-independent.
The multiplicative map `♯ : K♭ → K`, `f ↦ f 0`, is the *sharp* map.

Scholze's tilting equivalence asserts that `K ↦ K♭` is an equivalence between perfectoid
fields of mixed characteristic and perfectoid fields of characteristic `p`, compatible
with the Galois theory of the two sides.  Its *base case* — the content formalised and
proved below — is that on characteristic `p` perfectoid fields (i.e. perfect fields of
characteristic `p`) tilting is canonically the identity: the tilt is again a perfect ring
of characteristic `p`, and the sharp map is an isomorphism `K♭ ≃ K`.
-/

section Sequences

variable {K : Type*}

/-- A sequence of `p`-power-compatible elements: `f (n+1) ^ p = f n`. -/

lemma tiltSubring_toSubmonoid (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    (tiltSubring K p).toSubmonoid = tiltMonoid K p := rfl

/-- Evaluation at the `0`-th component, as a ring homomorphism `K♭ → K`. -/
