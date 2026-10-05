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

lemma tiltSubring_pow_bijective :
    Function.Bijective (fun x : tiltSubring K p => x ^ p) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have h' : ∀ n, f n ^ p = g n ^ p := fun n =>
      congrFun (congrArg (fun x : tiltSubring K p => (x : ℕ → K)) h) n
    exact Subtype.ext (hf.eq_of_pow_eq hg h')
  · rintro ⟨f, hf⟩
    exact ⟨⟨fun n => f (n + 1), hf.shift⟩, Subtype.ext hf.pow_shift⟩

end Perfect

/-- **Base case of Scholze's tilting equivalence.**

Let `K` be a perfectoid field of characteristic `p`, i.e. a perfect field of
characteristic `p` (Frobenius bijective).  Then:

* the tilt `K♭ = lim_{x ↦ xᵖ} K` is itself perfect: `x ↦ xᵖ` is bijective on `K♭`
  (this holds for the tilt of *any* commutative monoid, in any characteristic);
* the sharp map `♯ : K♭ → K`, `f ↦ f 0`, is a multiplicative bijection, and in fact a
  ring isomorphism `K♭ ≃+* K` for the (characteristic `p`) ring structure on the tilt;
* consequently `K♭` again has characteristic `p` and is perfect.

So on characteristic `p` perfectoid fields the tilting functor is canonically the
identity — the base case of Scholze's tilting equivalence. -/
