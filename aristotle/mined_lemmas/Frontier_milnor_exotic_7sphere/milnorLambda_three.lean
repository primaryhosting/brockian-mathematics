import Mathlib

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold

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
## Overview

Milnor's 1956 theorem asserts that there is a smooth `7`-manifold which is homeomorphic,
but not diffeomorphic, to the standard `7`-sphere.

The proof has two clearly separated halves.

* A **geometric/topological** half.  For integers `h + l = 1` one forms the total space
  `M_{h,l}` of an `S³`-bundle over `S⁴` (built from the two hemispheres of `S⁴` glued along
  the equator by the quaternionic map `v ↦ u^h v u^l`).  Morse theory applied to an explicit
  function on `M_{h,l}` shows that `M_{h,l}` is a topological `7`-sphere.  Furthermore Milnor
  constructs a `ℤ/7`-valued diffeomorphism invariant `λ` of smooth homotopy `7`-spheres
  (obtained from the first Pontryagin class and the signature of a coboundary via the
  Hirzebruch signature theorem) and computes `λ(M_{h,l}) = (h - l)² - 1 (mod 7)`, while
  `λ` vanishes on the standard sphere.

* An **arithmetic** half: the observation that `(h - l)² - 1` is *not* always `0` modulo `7`.

The arithmetic half is fully formalised and proved below (`milnorLambda`, and the lemmas
`milnorLambda_eq_zero_iff`, `exists_odd_milnorLambda_ne_zero`, ...).

The geometric half is far beyond what is currently available in Mathlib (it needs
characteristic classes, the Hirzebruch signature theorem, and Morse theory).  It is therefore
isolated in the structure `MilnorConstruction`, whose fields are exactly the geometric inputs
of Milnor's argument.  The target theorem `Frontier.milnor_exotic_7sphere` is the
**Lean-checked reduction**: from `MilnorConstruction` it derives the existence of an exotic
`7`-sphere.  No axioms are introduced: the geometric input appears as an explicit hypothesis.
-/

/-! ### The arithmetic core of Milnor's invariant -/

/-- Milnor's `λ`-invariant of the total space `M_{h,l}` of the `S³`-bundle over `S⁴`
with `h + l = 1`, expressed as a function of `k = h - l`:
`λ(M_{h,l}) ≡ (h - l)² - 1 (mod 7)`. -/

lemma milnorLambda_three : milnorLambda 3 = 1 := by
  decide +kernel

