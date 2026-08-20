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

theorem ae_eq_affine_of_integral_deriv2_smul_eq_zero {a b : ℝ} (hab : a < b) {f : ℝ → E}
    (hf : LocallyIntegrable f volume)
    (h : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, deriv (deriv g) x • f x = 0) :
    ∃ A B : E, ∀ᵐ x, x ∈ Set.Ioo a b → f x = x • A + B := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_isBumpOn_integral_eq_one hab
  set K : E := ∫ x, deriv χ x • f x with hK
  -- Step 1 : test functions with vanishing integral are derivatives of test functions.
  have step1 : ∀ ψ : ℝ → ℝ, IsBumpOn a b ψ → (∫ x, ψ x) = 0 →
      ∫ x, deriv ψ x • f x = 0 := by
    intro ψ hψ h0
    obtain ⟨hbump, hderiv⟩ := hψ.antideriv hab h0
    have hd : deriv (fun x => ∫ t in a..x, ψ t) = ψ := funext fun x => (hderiv x).deriv
    have h1 := h _ hbump
    rw [hd] at h1
    exact h1
  -- Step 2 : for a general test function, the pairing is proportional to its integral.
  have step2 : ∀ ψ : ℝ → ℝ, IsBumpOn a b ψ → ∫ x, deriv ψ x • f x = (∫ x, ψ x) • K := by
    intro ψ hψ
    set c : ℝ := ∫ x, ψ x with hc
    have hbump0 : IsBumpOn a b (fun x => ψ x - c * χ x) := hψ.sub (hχ.smul c)
    have hint0 : ∫ x, (ψ x - c * χ x) = 0 := by
      rw [integral_sub hψ.integrable ((hχ.smul c).integrable)]
      simp [integral_const_mul, hχ1, hc]
    have h1 := step1 _ hbump0 hint0
    have hd : deriv (fun x => ψ x - c * χ x) = fun x => deriv ψ x - c * deriv χ x :=
      funext fun x => ((hψ.hasDerivAt x).sub ((hχ.hasDerivAt x).const_mul c)).deriv
    rw [hd] at h1
    have hψf : Integrable (fun x => deriv ψ x • f x) volume :=
      hψ.deriv_isBumpOn.integrable_smul hf
    have hχf : Integrable (fun x => deriv χ x • f x) volume :=
      hχ.deriv_isBumpOn.integrable_smul hf
    have hexp : ∫ x, (deriv ψ x - c * deriv χ x) • f x
        = (∫ x, deriv ψ x • f x) - c • ∫ x, deriv χ x • f x := by
      have hpt : ∀ x, (deriv ψ x - c * deriv χ x) • f x
          = deriv ψ x • f x - c • (deriv χ x • f x) := by
        intro x; rw [sub_smul, mul_smul]
      simp_rw [hpt]
      have h2 : Integrable (fun x => c • (deriv χ x • f x)) volume := hχf.smul c
      rw [integral_sub hψf h2, integral_smul]
    rw [hexp] at h1
    rw [sub_eq_zero.mp h1, hK]
  -- Step 3 : subtract the linear part.
  set A : E := -K with hA
  have step3 : ∀ ψ : ℝ → ℝ, IsBumpOn a b ψ → ∫ x, deriv ψ x • (f x - x • A) = 0 := by
    intro ψ hψ
    have hψf : Integrable (fun x => deriv ψ x • f x) volume :=
      hψ.deriv_isBumpOn.integrable_smul hf
    have hmulint : Integrable (fun x => deriv ψ x * x) volume := by
      refine Continuous.integrable_of_hasCompactSupport
        (hψ.deriv_isBumpOn.continuous.mul continuous_id) ?_
      exact hψ.deriv_isBumpOn.compactSupport.mul_right
    have hlin : Integrable (fun x => deriv ψ x • (x • A)) volume := by
      have : (fun x => deriv ψ x • (x • A)) = fun x => (deriv ψ x * x) • A := by
        funext x; rw [smul_smul]
      rw [this]
      exact hmulint.smul_const A
    have hsplit : ∫ x, deriv ψ x • (f x - x • A)
        = (∫ x, deriv ψ x • f x) - ∫ x, deriv ψ x • (x • A) := by
      have hpt : ∀ x, deriv ψ x • (f x - x • A) = deriv ψ x • f x - deriv ψ x • (x • A) :=
        fun x => smul_sub _ _ _
      simp_rw [hpt]
      rw [integral_sub hψf hlin]
    have hlin2 : ∫ x, deriv ψ x • (x • A) = (-∫ x, ψ x) • A := by
      have hpt : ∀ x, deriv ψ x • (x • A) = (deriv ψ x * x) • A := fun x => by rw [smul_smul]
      simp_rw [hpt]
      rw [integral_smul_const, hψ.integral_deriv_mul_id hab]
    rw [hsplit, step2 ψ hψ, hlin2, hA, neg_smul, smul_neg, sub_neg_eq_add, add_neg_cancel]
  have hf₁ : LocallyIntegrable (fun x => f x - x • A) volume :=
    hf.sub ((continuous_id.smul continuous_const).locallyIntegrable)
  obtain ⟨B, hB⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero hab hf₁ step3
  refine ⟨A, B, ?_⟩
  filter_upwards [hB] with x hx hmem
  rw [eq_add_of_sub_eq (hx hmem), add_comm]

end Brockian.Weyl

import Brockian.Weyl.WeakAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Integration by parts against a primitive

For a locally integrable `h : ℝ → ℂ` and a test function `g` supported in `Ioo a b`, we
prove
`∫ g' x • (∫ t in c..x, h t) = -∫ g x • h x`,
i.e. the distributional derivative of the primitive of `h` is `h`.

The real-valued case is `Brockian.Weyl.integral_deriv_mul_primitive_real`; it uses the
Lebesgue differentiation theorem and integration by parts for absolutely continuous
functions.  The complex-valued case
`Brockian.Weyl.integral_deriv_smul_primitive` follows by applying real-linear
functionals.
-/

namespace Brockian.Weyl

open MeasureTheory Set Function

/-- A locally integrable function is interval integrable on every interval. -/
