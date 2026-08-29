import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

theorem heat_ge_kT_mul_entropy_drop
    [Nonempty B] (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (E : B → ℝ) (p : M → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m : M, p m = 1)
    (U : M × B ≃ M × B) :
    k * T * (entropy p - entropy (finalMem (1 / (k * T)) E p U))
      ≤ heat (1 / (k * T)) E p U := by
  have hkT : 0 < k * T := mul_pos hk hT
  have h := entropy_drop_le_beta_mul_heat (1 / (k * T)) E p hp hp1 U
  have h2 : k * T * (entropy p - entropy (finalMem (1 / (k * T)) E p U))
      ≤ k * T * (1 / (k * T) * heat (1 / (k * T)) E p U) :=
    mul_le_mul_of_nonneg_left h hkT.le
  have h3 : k * T * (1 / (k * T) * heat (1 / (k * T)) E p U)
      = heat (1 / (k * T)) E p U := by
    field_simp
  linarith

/-! ## Exact erasure is impossible: the invertible dynamics keeps full support

Because `U` is a bijection of the (finite) joint phase space and the bath's Gibbs
state is strictly positive, the final memory marginal is never a point mass.  This
is why Landauer's principle is stated below with an erasure error `eps`: the bound
`k T log 2` is approached in the limit of perfect erasure. -/

