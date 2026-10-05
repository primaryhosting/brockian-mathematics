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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-! ## The singular plane curves `y ^ n = x ^ (n + 1)` and their normalization -/

/-- The plane affine curve `C_n : y ^ n = x ^ (n + 1)` over a field `k`.
For `n ≥ 2` this curve has a single singular point, at the origin
(for `n = 2` it is the classical cuspidal cubic `y ^ 2 = x ^ 3`). -/

def cuspJacobian (k : Type*) [Field k] (n : ℕ) (p : k × k) : k × k :=
  (-((n + 1 : k) * p.1 ^ n), (n : k) * p.2 ^ (n - 1))

/-- Abstract notion of a **resolution of singularities of a plane curve
`C ⊆ 𝔸²` by the affine line `𝔸¹`**, with singular locus `S ⊆ C` and with `U ⊆ 𝔸¹`
the preimage of the smooth locus.

The data is a morphism `f : 𝔸¹ → 𝔸²` and a rational map `g` in the other direction
such that `f` is a bijection from the (smooth) affine line onto `C` — in particular
a finite, hence proper, birational morphism — restricting to an isomorphism
`U ≃ C ∖ S` over the smooth locus of `C`, with inverse `g` regular there. -/
structure IsPlaneCurveResolution {k : Type*} [Field k]
    (C S : Set (k × k)) (f : k → k × k) (g : k × k → k) (U : Set k) : Prop where
  /-- The singular locus is part of the curve. -/
  singular_subset : S ⊆ C
  /-- The resolution map lands in the curve. -/
  mapsTo : ∀ t, f t ∈ C
  /-- The resolution map is injective. -/
  injective : Function.Injective f
  /-- The resolution map hits every point of the curve. -/
  surjective : ∀ p ∈ C, ∃ t, f t = p
  /-- `U` is exactly the preimage of the smooth locus. -/
  preimage_smooth : ∀ t, f t ∉ S ↔ t ∈ U
  /-- `g` inverts `f` over the smooth locus. -/
  left_inv : ∀ t ∈ U, g (f t) = t
  /-- `f` inverts `g` over the smooth locus. -/
  right_inv : ∀ p ∈ C \ S, f (g p) = p
  /-- `g` maps the smooth locus into `U`. -/
  inv_mem : ∀ p ∈ C \ S, g p ∈ U

/-! ## Basic properties of the parametrization -/

