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

import Brockian.Weyl.Primitive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deficiency elements of a Sturm–Liouville operator are genuine ODE solutions

Let `q : ℝ → ℝ` be a continuous potential on an interval `(a, b)` and let `lam : ℂ`.  The
*minimal operator* associated with the formally symmetric differential expression
`τ u = -u'' + q u` is the restriction of `τ` to smooth compactly supported functions in
`(a, b)`.  A function `y ∈ L²(a, b)` lies in the deficiency space of the minimal operator
at `lam` exactly when it is orthogonal to the range of `τ - conj lam` on test functions,
that is when
`∫ conj (y x) * (-(g'' x) + q x * g x - conj lam * g x) = 0`
for every test function `g` supported in `(a, b)`; see `InDeficiencySpace`.

The main theorem `deficiencyRepresentsODE_of_weakRegularity` states that the deficiency
space is exactly the space of `L²` solutions of the ordinary differential equation
`-u'' + q u = lam * u`, i.e. every deficiency element is (a.e. equal to) a genuine, twice
differentiable, classical solution of the ODE.

The hard direction rests on the one-dimensional elliptic regularity statement
`weakRegularity` (Weyl's lemma): a locally integrable distributional solution of
`-y'' + q y = lam y` agrees a.e. with a classical solution.  It is proved here, so the
main theorem is unconditional.
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set Function Brockian.Weyl

/-- The smoothness exponent `∞`. -/
local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `IsODESolutionOn q lam s u` says that `u` is a classical solution of
`-u'' + q u = lam * u` on the set `s`: `u` is differentiable with a differentiable
derivative `u'` and `u'' = (q - lam) * u` on `s`. -/

theorem IsBumpOn.antideriv {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g)
    (h0 : ∫ x, g x = 0) :
    IsBumpOn a b (fun x => ∫ t in a..x, g t) ∧
      ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := by
  have hcont : Continuous g := hg.continuous
  have hderiv : ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := fun x =>
    (hcont.integral_hasStrictDerivAt a x).hasDerivAt
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hzero : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hsupp : ∀ x, x ∉ Set.Icc a₀ b₀ → (∫ t in a..x, g t) = 0 := by
    intro x hx
    rcases lt_or_ge x a₀ with hlt | hge
    · have hcongr : ∀ t ∈ Set.uIcc a x, g t = (0 : ℝ) := by
        intro t ht
        refine hzero t ?_
        simp only [mem_uIcc] at ht
        intro htI
        rcases ht with ht | ht
        · linarith [htI.1, ht.1]
        · linarith [htI.1, ht.2]
      calc (∫ t in a..x, g t) = ∫ _t in a..x, (0 : ℝ) :=
            intervalIntegral.integral_congr hcongr
        _ = 0 := by simp
    · have hxb : b₀ < x := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · linarith
        · exact hx
      have h1 : ∀ t ∉ Set.Ioc a x, g t = 0 := by
        intro t ht
        refine hzero t ?_
        simp only [mem_Ioc, not_and_or, not_le, not_lt] at ht
        intro htI
        rcases ht with ht | ht
        · linarith [htI.1]
        · linarith [htI.2]
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero h1, h0]
  refine ⟨⟨?_, ?_, ?_⟩, hderiv⟩
  · rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hd : deriv (fun x => ∫ t in a..x, g t) = g := funext fun x => (hderiv x).deriv
    rw [hd]
    exact hg.smooth
  · exact HasCompactSupport.intro (isCompact_Icc (a := a₀) (b := b₀)) hsupp
  · have h1 : tsupport (fun x => ∫ t in a..x, g t) ⊆ Set.Icc a₀ b₀ := by
      refine closure_minimal ?_ isClosed_Icc
      intro x hx
      by_contra hxc
      exact hx (hsupp x hxc)
    exact h1.trans (Set.Icc_subset_Ioo ha₀ hb₀)

/-- There is a bump function on `Ioo a b` with integral one. -/
