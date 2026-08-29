/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

theorem nbhd_nbhd_subset {r : ℝ} {X : Set Site} :
    nbhd 1 (nbhd r X) ⊆ nbhd (r + 1) X := by
  rintro z ⟨p, ⟨x, hx, hpx⟩, hzp⟩
  refine ⟨x, hx, ?_⟩
  have := dist_triangle z p x
  linarith

variable (loc : Set Site → Set A)

/-- Locality structure: monotone family of subsets of the algebra, closed under products,
with algebras attached to disjoint regions commuting. -/
structure LocalStructure : Prop where
  mono : ∀ ⦃S T : Set Site⦄, S ⊆ T → loc S ⊆ loc T
  mul_mem : ∀ (S : Set Site), ∀ x ∈ loc S, ∀ y ∈ loc S, x * y ∈ loc S
  commute : ∀ (S T : Set Site), Disjoint S T → ∀ x ∈ loc S, ∀ y ∈ loc T, x * y = y * x

variable {loc}

/-- **Support propagation (strict light cone).** After `n` layers of gates each supported in a
region of diameter at most `1`, an observable supported in `X` is supported in the
`n`-neighbourhood of `X`. -/
