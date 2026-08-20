import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Quadratic-like maps (Douady–Hubbard)

A *quadratic-like map* is a triple `(f, U, V)` where `U ⋐ V` are bounded, connected open
subsets of `ℂ` and `f : U → V` is a proper holomorphic map of degree `2`.  Degree two is
encoded here concretely: `f` has a unique critical point `c ∈ U`, the fibre over the critical
value `f c` is the singleton `{c}`, and every other fibre over `V` consists of exactly two
points.
-/

/-- A quadratic-like map in the sense of Douady–Hubbard, presented as a globally defined
function `f : ℂ → ℂ` together with the data of the domains `U ⋐ V`.  Only the behaviour of
`f` on `U` is constrained. -/
structure QuadraticLike where
  /-- The small domain. -/
  U : Set ℂ
  /-- The large domain. -/
  V : Set ℂ
  /-- The map. -/
  f : ℂ → ℂ
  /-- The critical point. -/
  critical : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_U : IsConnected U
  isConnected_V : IsConnected V
  isBounded_V : Bornology.IsBounded V
  /-- `U` is compactly contained in `V`. -/
  closure_U_subset : closure U ⊆ V
  differentiableOn : DifferentiableOn ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is proper. -/
  properOn : ∀ ⦃K : Set ℂ⦄, K ⊆ V → IsCompact K → IsCompact (U ∩ f ⁻¹' K)
  critical_mem : critical ∈ U
  /-- The fibre over the critical value is a single (doubled) point. -/
  fiber_critical : U ∩ f ⁻¹' {f critical} = {critical}
  /-- Every non-critical fibre over `V` has exactly two points: `f` has degree two. -/
  fiber_card : ∀ w ∈ V, w ≠ f critical → (U ∩ f ⁻¹' {w}).ncard = 2
  deriv_critical : deriv f critical = 0
  unique_critical : ∀ z ∈ U, deriv f z = 0 → z = critical

namespace QuadraticLike

variable (Q : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/

def C : Set ℂ := Q.U ∩ Q.f ⁻¹' (closure Q.U)

