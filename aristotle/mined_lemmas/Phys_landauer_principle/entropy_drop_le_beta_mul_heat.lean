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

theorem entropy_drop_le_beta_mul_heat :
    entropy p - entropy (finalMem beta E p U) ≤ beta * heat beta E p U := by
  have hgnn : ∀ x : M × B, 0 ≤ finalMem beta E p U x.1 * gibbs beta E x.2 :=
    fun x => mul_nonneg (finalMem_nonneg beta E p hp U x.1) (gibbs_pos beta E x.2).le
  have hsupp : ∀ x : M × B, finalMem beta E p U x.1 * gibbs beta E x.2 = 0 →
      finalJoint beta E p U x = 0 := by
    rintro ⟨m, b⟩ hx
    have h0 : finalMem beta E p U m = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · exact h
      · exact absurd h (ne_of_gt (gibbs_pos beta E b))
    exact le_antisymm (by simpa [h0] using finalJoint_le_finalMem beta E p hp U m b)
      (finalJoint_nonneg beta E p hp U (m, b))
  have hgsum : ∑ x : M × B, finalMem beta E p U x.1 * gibbs beta E x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, gibbs_sum, mul_one]
    exact finalMem_sum beta E p hp1 U
  have hKL := zero_le_relEntropy (finalJoint beta E p U)
    (fun x : M × B => finalMem beta E p U x.1 * gibbs beta E x.2)
    (finalJoint_nonneg beta E p hp U) hgnn hsupp
    (by rw [hgsum, finalJoint_sum beta E p hp1 U])
  rw [sum_finalJoint_mul_log beta E p hp hp1 U,
    sum_finalJoint_mul_log_prod beta E p hp U,
    sum_gibbs_mul_log beta E,
    sum_finalJoint_mul_log_gibbs beta E p hp1 U] at hKL
  unfold entropy heat
  linarith

end Setup

/-! ## The Landauer bound -/

