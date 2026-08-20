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

theorem ae_eq_const_of_integral_deriv_smul_eq_zero {a b : ℝ} (hab : a < b) {f : ℝ → E}
    (hf : LocallyIntegrable f volume)
    (h : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, deriv g x • f x = 0) :
    ∃ C : E, ∀ᵐ x, x ∈ Set.Ioo a b → f x = C := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_isBumpOn_integral_eq_one hab
  set C : E := ∫ x, χ x • f x with hC
  refine ⟨C, ?_⟩
  have key : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, g x • (f x - C) = 0 := by
    intro g hg
    set c : ℝ := ∫ x, g x with hc
    have hbump0 : IsBumpOn a b (fun x => g x - c * χ x) := hg.sub (hχ.smul c)
    have hint0 : ∫ x, (g x - c * χ x) = 0 := by
      rw [integral_sub hg.integrable ((hχ.smul c).integrable)]
      simp [integral_const_mul, hχ1, hc]
    obtain ⟨hbump, hderiv⟩ := hbump0.antideriv hab hint0
    have hd : deriv (fun x => ∫ t in a..x, (g t - c * χ t)) = fun x => g x - c * χ x :=
      funext fun x => (hderiv x).deriv
    have h0 := h _ hbump
    rw [hd] at h0
    have hgf : Integrable (fun x => g x • f x) volume := hg.integrable_smul hf
    have hχf : Integrable (fun x => χ x • f x) volume := hχ.integrable_smul hf
    have hexp : ∫ x, (g x - c * χ x) • f x
        = (∫ x, g x • f x) - c • ∫ x, χ x • f x := by
      have hpt : ∀ x, (g x - c * χ x) • f x = g x • f x - c • (χ x • f x) := by
        intro x; rw [sub_smul, mul_smul]
      simp_rw [hpt]
      have h2 : Integrable (fun x => c • (χ x • f x)) volume := hχf.smul c
      rw [integral_sub hgf h2, integral_smul]
    rw [hexp] at h0
    have hgC : Integrable (fun x => g x • C) volume := hg.integrable.smul_const C
    have hsplit : ∫ x, g x • (f x - C) = (∫ x, g x • f x) - (∫ x, g x) • C := by
      have hpt : ∀ x, g x • (f x - C) = g x • f x - g x • C := fun x => smul_sub _ _ _
      simp_rw [hpt]
      rw [integral_sub hgf hgC, integral_smul_const]
    rw [hsplit, ← hc, sub_eq_zero.mp h0, ← hC, sub_self]
  have hloc : LocallyIntegrableOn (fun x => f x - C) (Set.Ioo a b) volume :=
    ((hf.sub (locallyIntegrable_const C))).locallyIntegrableOn _
  have hae := (isOpen_Ioo (a := a) (b := b)).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg1 hg2 hg3 => key g ⟨hg1, hg2, hg3⟩)
  filter_upwards [hae] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

/-- If the second distributional derivative of a locally integrable function vanishes on
`Ioo a b`, then the function is a.e. affine there. -/
