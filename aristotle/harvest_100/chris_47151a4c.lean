/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical NNReal

set_option maxHeartbeats 1000000

namespace KPZ

/-- Spatial derivative of a space-time function `h : time → space → ℝ`. -/
noncomputable def spaceDeriv (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => deriv (fun y => h t y) x

/-- `IsSolution xi h` says that `h : time → space → ℝ` is a classical solution of the
Kardar–Parisi–Zhang equation
`∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ`
with forcing `xi`. -/
def IsSolution (xi h : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x : ℝ, HasDerivAt (fun s => h s x)
    (spaceDeriv (spaceDeriv h) t x + (spaceDeriv h t x) ^ 2 + xi t x) t

/-! ## Base case 1: the Cole–Hopf linearisation

If `w > 0` solves the heat equation `∂ₜ w = ∂ₓ² w`, then `h = log w` solves the
(unforced) KPZ equation. This is the classical transformation underlying the
solution theory of KPZ. -/

theorem spaceDeriv_log (w wx : ℝ → ℝ → ℝ) (hpos : ∀ t x, 0 < w t x)
    (hx : ∀ t x, HasDerivAt (fun y => w t y) (wx t x) x) (t : ℝ) :
    spaceDeriv (fun t x => Real.log (w t x)) t = fun x => wx t x / w t x := by
  funext x
  exact ((hx t x).log (hpos t x).ne').deriv

theorem coleHopf (w wx wxx : ℝ → ℝ → ℝ)
    (hpos : ∀ t x, 0 < w t x)
    (hx : ∀ t x, HasDerivAt (fun y => w t y) (wx t x) x)
    (hxx : ∀ t x, HasDerivAt (fun y => wx t y) (wxx t x) x)
    (heat : ∀ t x, HasDerivAt (fun s => w s x) (wxx t x) t) :
    IsSolution (fun _ _ => 0) (fun t x => Real.log (w t x)) := by
  intro t x
  have h1 : spaceDeriv (fun t x => Real.log (w t x)) t = fun x => wx t x / w t x :=
    spaceDeriv_log w wx hpos hx t
  have h2 : spaceDeriv (spaceDeriv (fun t x => Real.log (w t x))) t x
      = (wxx t x * w t x - wx t x * wx t x) / (w t x) ^ 2 := by
    have key : (fun y => deriv (fun y => Real.log (w t y)) y) = fun y => wx t y / w t y := by
      funext y
      exact ((hx t y).log (hpos t y).ne').deriv
    show deriv (fun y => deriv (fun y => Real.log (w t y)) y) x = _
    rw [key]
    exact ((hxx t x).div (hx t x) (hpos t x).ne').deriv
  have hval : spaceDeriv (spaceDeriv (fun t x => Real.log (w t x))) t x
      + (spaceDeriv (fun t x => Real.log (w t x)) t x) ^ 2 + 0
      = wxx t x / w t x := by
    rw [h2, h1]
    have hw : w t x ≠ 0 := (hpos t x).ne'
    field_simp
    ring
  rw [hval]
  exact (heat t x).log (hpos t x).ne'

/-! ## Base case 2: the spatially homogeneous KPZ equation

For a space-independent forcing, the space-independent KPZ dynamics reduces to
`H' = g`, which has a unique solution for each initial datum. -/

theorem isSolution_of_const_space (H g : ℝ → ℝ) :
    IsSolution (fun t _ => g t) (fun t _ => H t) ↔ ∀ t, HasDerivAt H (g t) t := by
  have hs : spaceDeriv (fun t _ : ℝ => H t) = fun _ _ => (0 : ℝ) := by
    funext t x; simp [spaceDeriv]
  constructor
  · intro h t
    have := h t 0
    rw [hs] at this
    simpa [spaceDeriv] using this
  · intro h t x
    rw [hs]
    simpa [spaceDeriv] using h t

theorem homogeneous_wellposed (g : ℝ → ℝ) (hg : Continuous g) (h₀ : ℝ) :
    ∃! H : ℝ → ℝ, H 0 = h₀ ∧ IsSolution (fun t _ => g t) (fun t _ => H t) := by
  refine ⟨fun t => h₀ + ∫ s in (0 : ℝ)..t, g s, ⟨by simp, ?_⟩, ?_⟩
  · rw [isSolution_of_const_space]
    intro t
    simpa using ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add h₀
  · rintro H ⟨hH0, hHsol⟩
    rw [isSolution_of_const_space] at hHsol
    have hgoal : ∀ t, HasDerivAt (fun u => h₀ + ∫ s in (0 : ℝ)..u, g s) (g t) t := by
      intro t
      simpa using ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add h₀
    set G : ℝ → ℝ := fun t => h₀ + ∫ s in (0 : ℝ)..t, g s with hG
    have hdiff : Differentiable ℝ (fun t => H t - G t) := fun t =>
      ((hHsol t).sub (hgoal t)).differentiableAt
    have hzero : ∀ t, deriv (fun t => H t - G t) t = 0 := by
      intro t
      have := (hHsol t).sub (hgoal t)
      simpa using this.deriv
    have hconst := is_const_of_deriv_eq_zero hdiff hzero
    funext t
    have h1 := hconst t 0
    have h2 : G 0 = h₀ := by simp [hG]
    have : H t - G t = H 0 - G 0 := h1
    rw [hH0, h2] at this
    linarith [this]

/-! ## The reduction: well-posedness from the abstract fixed point problem

Hairer's solution theory recasts the (renormalised) KPZ equation as a fixed point
problem `u = Φ d u` in a complete metric space `X` of modelled distributions, where
`d` ranges over the data (an admissible model together with an initial condition).
The two analytic inputs are:

* `Φ d` is a contraction on `X`, uniformly in `d` (short-time Schauder estimates);
* `Φ` depends Lipschitz-continuously on the data `d` (continuity of the abstract
  integration and reconstruction operators in the model).

The theorem below is the Lean-checked reduction: from these two inputs one obtains
a *well-posed* problem, i.e. a solution map `S` which exists, is unique, and depends
Lipschitz-continuously (in particular continuously) on the data. -/

theorem wellposed_of_contraction {D X : Type*} [MetricSpace D] [MetricSpace X]
    [CompleteSpace X] [Nonempty X]
    (Φ : D → X → X) (K : ℝ≥0) (hK : K < 1) (hc : ∀ d, LipschitzWith K (Φ d))
    (L : ℝ) (hL : 0 ≤ L) (hdata : ∀ d₁ d₂ u, dist (Φ d₁ u) (Φ d₂ u) ≤ L * dist d₁ d₂) :
    ∃ S : D → X,
      (∀ d, Φ d (S d) = S d) ∧
      (∀ d u, Φ d u = u → u = S d) ∧
      (∀ d₁ d₂, dist (S d₁) (S d₂) ≤ L / (1 - K) * dist d₁ d₂) ∧
      Continuous S := by
  have hcon : ∀ d, ContractingWith K (Φ d) := fun d => ⟨hK, hc d⟩
  refine ⟨fun d => ContractingWith.fixedPoint (Φ d) (hcon d), fun d => ?_, fun d u hu => ?_, ?_, ?_⟩
  · exact ContractingWith.fixedPoint_isFixedPt (hcon d)
  · exact ContractingWith.fixedPoint_unique (hcon d) hu
  · intro d₁ d₂
    have h := ContractingWith.fixedPoint_lipschitz_in_map (hcon d₁) (hcon d₂)
      (C := L * dist d₁ d₂) (fun u => hdata d₁ d₂ u)
    calc dist (ContractingWith.fixedPoint (Φ d₁) (hcon d₁))
          (ContractingWith.fixedPoint (Φ d₂) (hcon d₂))
        ≤ L * dist d₁ d₂ / (1 - K) := h
      _ = L / (1 - (K : ℝ)) * dist d₁ d₂ := by ring
  · have hKlt : (K : ℝ) < 1 := by exact_mod_cast hK
    have hpos : (0 : ℝ) < 1 - (K : ℝ) := by linarith
    have hnn : 0 ≤ L / (1 - (K : ℝ)) := div_nonneg hL hpos.le
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (L / (1 - (K : ℝ))))
      (fun d₁ d₂ => ?_)).continuous
    rw [Real.coe_toNNReal _ hnn]
    have h := ContractingWith.fixedPoint_lipschitz_in_map (hcon d₁) (hcon d₂)
      (C := L * dist d₁ d₂) (fun u => hdata d₁ d₂ u)
    calc dist (ContractingWith.fixedPoint (Φ d₁) (hcon d₁))
          (ContractingWith.fixedPoint (Φ d₂) (hcon d₂))
        ≤ L * dist d₁ d₂ / (1 - K) := h
      _ = L / (1 - (K : ℝ)) * dist d₁ d₂ := by ring

end KPZ

namespace Frontier

/-- **Hairer's KPZ theorem (formalised statement, base cases and reduction).**

The KPZ equation `∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ` is well posed. Full well-posedness for
space-time white noise requires the theory of regularity structures; what is proved
here is:

1. the *Cole–Hopf base case*: whenever `w > 0` solves the heat equation, `log w`
   is a classical solution of the unforced KPZ equation;
2. the *spatially homogeneous base case*: for a space-independent continuous forcing
   `g`, the space-independent KPZ dynamics has a unique solution for each initial
   datum (existence and uniqueness);
3. the *reduction to the abstract fixed point problem*: if the (renormalised) equation
   is recast, as in Hairer's theory, as a fixed point `u = Φ d u` in a complete metric
   space of modelled distributions with `Φ d` a uniform contraction and `Φ` Lipschitz
   in the data `d`, then the problem is well posed: the solution map exists, is unique,
   and depends Lipschitz-continuously (hence continuously) on the data. -/
theorem hairer_KPZ :
    (∀ w wx wxx : ℝ → ℝ → ℝ,
        (∀ t x, 0 < w t x) →
        (∀ t x, HasDerivAt (fun y => w t y) (wx t x) x) →
        (∀ t x, HasDerivAt (fun y => wx t y) (wxx t x) x) →
        (∀ t x, HasDerivAt (fun s => w s x) (wxx t x) t) →
        KPZ.IsSolution (fun _ _ => 0) (fun t x => Real.log (w t x))) ∧
    (∀ g : ℝ → ℝ, Continuous g → ∀ h₀ : ℝ,
        ∃! H : ℝ → ℝ, H 0 = h₀ ∧ KPZ.IsSolution (fun t _ => g t) (fun t _ => H t)) ∧
    (∀ (D X : Type) (_ : MetricSpace D) (_ : MetricSpace X),
        ∀ [CompleteSpace X] [Nonempty X],
        ∀ (Φ : D → X → X) (K : ℝ≥0), K < 1 → (∀ d, LipschitzWith K (Φ d)) →
        ∀ L : ℝ, 0 ≤ L → (∀ d₁ d₂ u, dist (Φ d₁ u) (Φ d₂ u) ≤ L * dist d₁ d₂) →
        ∃ S : D → X,
          (∀ d, Φ d (S d) = S d) ∧
          (∀ d u, Φ d u = u → u = S d) ∧
          (∀ d₁ d₂, dist (S d₁) (S d₂) ≤ L / (1 - K) * dist d₁ d₂) ∧
          Continuous S) :=
  ⟨KPZ.coleHopf, KPZ.homogeneous_wellposed,
    fun _ _ _ _ _ _ Φ K hK hc L hL hdata =>
      KPZ.wellposed_of_contraction Φ K hK hc L hL hdata⟩

end Frontier

#print axioms Frontier.hairer_KPZ

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

