import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem M_unique {w w' : FreeGroup (Fin 2)} {m m' : E} (hm : m ∈ M) (hm' : m' ∈ M)
    (h : phi w m = phi w' m') : w = w' ∧ m = m' := by
  obtain ⟨q, rfl⟩ := hm
  obtain ⟨q', rfl⟩ := hm'
  have hrel : orbitSetoid.r (Quotient.out q) (Quotient.out q') := by
    refine ⟨w'⁻¹ * w, ?_⟩
    rw [map_mul, map_inv]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [h]
    exact (phi w').symm_apply_apply _
  have hqq : q = q' := by
    have := Quotient.sound hrel
    rwa [Quotient.out_eq, Quotient.out_eq] at this
  subst hqq
  have hfix : phi (w'⁻¹ * w) ((Quotient.out q : ↥SX) : E) = ((Quotient.out q : ↥SX) : E) := by
    rw [map_mul, map_inv]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [h]
    exact (phi w').symm_apply_apply _
  have hone := phi_free (M_subset ⟨q, rfl⟩) hfix
  exact ⟨(inv_mul_eq_one.mp hone).symm, rfl⟩

/-- The part of `SX` corresponding to a set of group elements. -/
