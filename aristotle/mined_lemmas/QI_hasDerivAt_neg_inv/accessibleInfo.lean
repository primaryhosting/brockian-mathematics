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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


noncomputable def accessibleInfo {X : Type*} (Y : Type*) [Fintype X] [Fintype Y]
    (p : X → ℝ) (ρ : X → Mat n) : ℝ :=
  ⨆ E : {E : Y → Mat n // IsPOVM E}, mutualInformation (measureDist p ρ E.1)

end QI

import RequestProject.QI.Resolvent
import RequestProject.QI.ScalarIntegrals

/-!
# The BKM quadratic form

For a positive definite `ω` and a Hermitian `Δ` we set
`bkm ω Δ = ∫₀^∞ Tr (Δ (ω+t)⁻¹ Δ (ω+t)⁻¹) dt`,
the Bogoliubov–Kubo–Mori quadratic form.  In the eigenbasis of `ω` it is
`∑ᵢⱼ |Δᵢⱼ|² / L(μᵢ, μⱼ)` where `L` is the logarithmic mean of the eigenvalues.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω Δ : Mat n}

/-- The BKM (Bogoliubov–Kubo–Mori) quadratic form of `Δ` at the positive definite matrix `ω`. -/
