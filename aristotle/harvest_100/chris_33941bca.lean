/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A self-contained development of the mean value theorem: the interior extremum
principle gives Rolle's theorem, and Rolle's theorem applied to an auxiliary
function gives the mean value theorem.
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

namespace Math

open Set

/-- If `f` attains a maximum over `[a, b]` at an interior point `x`, its derivative
there vanishes. -/
theorem deriv_eq_zero_of_isMaxOn_Icc {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hmax : IsMaxOn f (Icc a b) x) : deriv f x = 0 :=
  (hmax.isLocalMax (Icc_mem_nhds hx.1 hx.2)).deriv_eq_zero

/-- If `f` attains a minimum over `[a, b]` at an interior point `x`, its derivative
there vanishes. -/
theorem deriv_eq_zero_of_isMinOn_Icc {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hmin : IsMinOn f (Icc a b) x) : deriv f x = 0 :=
  (hmin.isLocalMin (Icc_mem_nhds hx.1 hx.2)).deriv_eq_zero

/-- A function that is constant on `[a, b]` has vanishing derivative at every interior
point of the interval. -/
theorem deriv_eq_zero_of_constantOn_Icc {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hconst : ∀ z ∈ Icc a b, f z = f a) : deriv f c = 0 := by
  have hev : f =ᶠ[nhds c] (fun _ : ℝ => f a) := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with z hz
    exact hconst z (Ioo_subset_Icc_self hz)
  rw [hev.deriv_eq, deriv_const]

/-- **Rolle's theorem.** A function continuous on `[a, b]` (with `a < b`) taking equal
values at the endpoints has a critical point in the open interval `(a, b)`.  No
differentiability hypothesis is needed: at a point where `f` is not differentiable,
`deriv f` is `0` by convention. -/
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hfab : f a = f b) : ∃ c ∈ Ioo a b, deriv f c = 0 := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.2 hab.le
  obtain ⟨x, hxmem, hxmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  obtain ⟨y, hymem, hymin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  -- If either extremum is attained at an interior point we are done.
  by_cases hxi : x ∈ Ioo a b
  · exact ⟨x, hxi, deriv_eq_zero_of_isMaxOn_Icc hxi hxmax⟩
  by_cases hyi : y ∈ Ioo a b
  · exact ⟨y, hyi, deriv_eq_zero_of_isMinOn_Icc hyi hymin⟩
  -- Otherwise both extrema are at endpoints, so `f` is constant on `[a, b]`.
  have hxa : f x = f a := by
    rcases eq_or_lt_of_le hxmem.1 with h | h
    · rw [← h]
    · rcases eq_or_lt_of_le hxmem.2 with h' | h'
      · rw [h', hfab]
      · exact absurd ⟨h, h'⟩ hxi
  have hya : f y = f a := by
    rcases eq_or_lt_of_le hymem.1 with h | h
    · rw [← h]
    · rcases eq_or_lt_of_le hymem.2 with h' | h'
      · rw [h', hfab]
      · exact absurd ⟨h, h'⟩ hyi
  have hconst : ∀ z ∈ Icc a b, f z = f a := by
    intro z hz
    have h1 : f z ≤ f x := hxmax hz
    have h2 : f y ≤ f z := hymin hz
    rw [hxa] at h1
    rw [hya] at h2
    linarith
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact ⟨(a + b) / 2, hc, deriv_eq_zero_of_constantOn_Icc hc hconst⟩

/-- The derivative of the auxiliary function `f x - s * x` at an interior point where `f`
is differentiable. -/
theorem deriv_sub_linear {f : ℝ → ℝ} {s c : ℝ} (hf : DifferentiableAt ℝ f c) :
    deriv (fun x : ℝ => f x - s * x) c = deriv f c - s := by
  have h : HasDerivAt (fun x : ℝ => f x - s * x) (deriv f c - s * 1) c :=
    hf.hasDerivAt.sub ((hasDerivAt_id c).const_mul s)
  simpa using h.deriv

/-- **Mean value theorem.** If `f : ℝ → ℝ` is continuous on `[a, b]` and differentiable on
the open interval `(a, b)` (with `a < b`), then there is a point `c` strictly between `a`
and `b` at which the derivative of `f` equals the average slope `(f b - f a) / (b - a)`. -/
theorem mean_value (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  set s : ℝ := (f b - f a) / (b - a) with hs
  set g : ℝ → ℝ := fun x => f x - s * x with hg
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have hgcont : ContinuousOn g (Icc a b) :=
    hcont.sub ((continuousOn_const).mul continuousOn_id)
  have hgab : g a = g b := by
    have : s * (b - a) = f b - f a := by
      rw [hs, div_mul_cancel₀ _ hba]
    simp only [hg]
    linarith [this]
  obtain ⟨c, hc, hgc⟩ := rolle hab hgcont hgab
  refine ⟨c, hc, ?_⟩
  have hfc : DifferentiableAt ℝ f c := hdiff.differentiableAt (Ioo_mem_nhds hc.1 hc.2)
  have : deriv f c - s = 0 := by
    rw [← deriv_sub_linear (s := s) hfc]
    exact hgc
  linarith

/-- **Mean value theorem** for a function differentiable on all of `ℝ` (in particular on
`[a, b]`): there is `c ∈ (a, b)` with `f' c = (f b - f a) / (b - a)`. -/
theorem mean_value_of_differentiable (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value f hab hf.continuous.continuousOn hf.differentiableOn

end Math

