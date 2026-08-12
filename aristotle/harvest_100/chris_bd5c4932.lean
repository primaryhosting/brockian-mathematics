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

open Polynomial

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root.

The proof is the classical Liouville argument: if `p` never vanished, then `1/p` would be an
entire function, bounded because `‖p.eval ·‖` attains a positive global minimum, hence constant
by Liouville's theorem; but `‖p.eval z‖ → ∞` as `‖z‖ → ∞` since `p` is nonconstant. -/
theorem fta_algebra {p : Polynomial ℂ} (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨x₀, hx₀⟩ := p.exists_forall_norm_le
  have hpos : 0 < ‖p.eval x₀‖ := norm_pos_iff.2 (hno x₀)
  have hdiff : Differentiable ℂ (fun z : ℂ => (p.eval z)⁻¹) :=
    fun z => ((Polynomial.differentiable_aeval p z).inv (hno z))
  have hbdd : Bornology.IsBounded (Set.range fun z : ℂ => (p.eval z)⁻¹) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(‖p.eval x₀‖)⁻¹, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [norm_inv]
    exact inv_anti₀ hpos (hx₀ z)
  have heval : ∀ z : ℂ, p.eval z = p.eval 0 :=
    fun z => inv_inj.mp (hdiff.apply_eq_apply_of_bounded hbdd z 0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖p.eval (n : ℂ)‖) Filter.atTop Filter.atTop := by
    apply p.tendsto_norm_atTop hp
    simpa using tendsto_natCast_atTop_atTop (R := ℝ)
  have hconst : Filter.Tendsto (fun _ : ℕ => ‖p.eval (0:ℂ)‖) Filter.atTop Filter.atTop := by
    simpa [heval] using htend
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds hconst

end Math

#print axioms Math.fta_algebra

