/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Set

namespace Math

/-- If `f` is constant on an open interval, its derivative vanishes at interior points. -/
theorem deriv_eq_zero_of_constant_on_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hconst : ∀ x ∈ Ioo a b, f x = f c) : deriv f c = 0 := by
  have h : f =ᶠ[nhds c] fun _ => f c := by
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx using hconst x hx
  rw [h.deriv_eq, deriv_const]

/-- **Rolle's theorem**: a function continuous on `[a,b]` taking equal values at the endpoints
has a critical point in `(a,b)`.

(Differentiability is not needed as a hypothesis: at a point where `f` is not differentiable,
Mathlib's junk value convention already gives `deriv f = 0`.) -/
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfab : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.2 hab.le
  obtain ⟨xM, hxM, hMax⟩ := isCompact_Icc.exists_isMaxOn hne hfc
  obtain ⟨xm, hxm, hMin⟩ := isCompact_Icc.exists_isMinOn hne hfc
  by_cases hM : xM ∈ Ioo a b
  · refine ⟨xM, hM, ?_⟩
    have : IsLocalMax f xM := by
      filter_upwards [isOpen_Ioo.mem_nhds hM] with y hy
      exact hMax (Ioo_subset_Icc_self hy)
    exact this.deriv_eq_zero
  by_cases hm : xm ∈ Ioo a b
  · refine ⟨xm, hm, ?_⟩
    have : IsLocalMin f xm := by
      filter_upwards [isOpen_Ioo.mem_nhds hm] with y hy
      exact hMin (Ioo_subset_Icc_self hy)
    exact this.deriv_eq_zero
  -- both extrema are attained at the endpoints, so `f` is constant
  have hend : ∀ x ∈ Icc a b, x ∉ Ioo a b → f x = f a := by
    intro x hx hx'
    rcases eq_or_lt_of_le hx.1 with h | h
    · exact congrArg f h.symm
    · have : x = b := le_antisymm hx.2 (not_lt.1 fun hb => hx' ⟨h, hb⟩)
      rw [this, hfab]
  have hMa : f xM = f a := hend xM hxM hM
  have hma : f xm = f a := hend xm hxm hm
  have hconstIcc : ∀ x ∈ Icc a b, f x = f a := by
    intro x hx
    have h1 : f x ≤ f a := hMa ▸ hMax hx
    have h2 : f a ≤ f x := hma ▸ hMin hx
    exact le_antisymm h1 h2
  refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  refine deriv_eq_zero_of_constant_on_Ioo (a := a) (b := b) ⟨by linarith, by linarith⟩ ?_
  intro x hx
  rw [hconstIcc x (Ioo_subset_Icc_self hx),
    hconstIcc ((a + b) / 2) ⟨by linarith, by linarith⟩]

/-- **Lagrange's Mean Value Theorem.** If `f : ℝ → ℝ` is continuous on `[a, b]` (with `a < b`)
and differentiable on the open interval `(a, b)`, then there is a point `c ∈ (a, b)` with
`f' c = (f b - f a) / (b - a)`. -/
theorem mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  set k : ℝ := (f b - f a) / (b - a) with hk
  set g : ℝ → ℝ := fun x => f x - k * x with hg
  have hgc : ContinuousOn g (Icc a b) :=
    hfc.sub ((continuousOn_const).mul continuousOn_id)
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have hgab : g a = g b := by
    have h1 : k * (b - a) = f b - f a := div_mul_cancel₀ _ hba
    have h2 : k * b - k * a = f b - f a := by rw [← h1]; ring
    simp only [hg]
    linarith
  obtain ⟨c, hc, hc0⟩ := rolle hab hgc hgab
  refine ⟨c, hc, ?_⟩
  have hfdc : DifferentiableAt ℝ f c := (hfd c hc).differentiableAt (isOpen_Ioo.mem_nhds hc)
  have hderiv : deriv g c = deriv f c - k := by
    have h1 : HasDerivAt (fun x : ℝ => k * x) k c := by
      simpa using (hasDerivAt_id c).const_mul k
    exact (hfdc.hasDerivAt.sub h1).deriv
  rw [hderiv] at hc0
  linarith [hc0]

end Math

#print axioms Math.mean_value

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

