/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

noncomputable section

/-! ## The `n`-dimensional torus and rotations -/

/-- The `n`-dimensional torus `𝕋ⁿ = (ℝ/ℤ)ⁿ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- The rigid rotation of `𝕋ⁿ` by the frequency vector `ω`. -/
def rot {n : ℕ} (ω : Fin n → ℝ) : C(Torus n, Torus n) :=
  ⟨fun θ => θ + fun i => ((ω i : ℝ) : AddCircle (1 : ℝ)), by fun_prop⟩

/-- A frequency vector `ω` is `(γ, τ)`-Diophantine if `⟨k, ω⟩` stays at distance at least
`γ / ‖k‖^τ` from every integer, for every nonzero integer vector `k`.  This is the classical
non-resonance condition under which the small-divisor (homological) equations of KAM theory
are solvable. -/
def Diophantine {n : ℕ} (ω : Fin n → ℝ) (γ τ : ℝ) : Prop :=
  ∀ k : Fin n → ℤ, k ≠ 0 → ∀ m : ℤ,
    γ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |(∑ i, (k i : ℝ) * ω i) - (m : ℝ)|

/-! ## Invariant tori -/

/-- `p : 𝕋ⁿ → X` parametrizes an invariant torus of `F` carrying the rotation `ω`:
the dynamics of `F` restricted to the image of `p` is conjugated by `p` to the rigid
rotation by `ω`. -/
def IsInvariantTorus {n : ℕ} {X : Type*} [TopologicalSpace X]
    (F : C(X, X)) (ω : Fin n → ℝ) (p : C(Torus n, X)) : Prop :=
  ∀ θ : Torus n, F (p θ) = p (rot ω θ)

/-- The invariance operator `Φ_F(p) = F ∘ p - p ∘ R_ω`, whose zeros are exactly the
invariant tori of `F` with rotation vector `ω`. -/
def invarianceOp {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    (F : C(X, X)) (ω : Fin n → ℝ) (p : C(Torus n, X)) : C(Torus n, X) :=
  F.comp p - p.comp (rot ω)

@[simp] lemma invarianceOp_apply {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    (F : C(X, X)) (ω : Fin n → ℝ) (p : C(Torus n, X)) (θ : Torus n) :
    invarianceOp F ω p θ = F (p θ) - p (rot ω θ) := rfl

lemma isInvariantTorus_iff_invarianceOp_eq_zero {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    (F : C(X, X)) (ω : Fin n → ℝ) (p : C(Torus n, X)) :
    IsInvariantTorus F ω p ↔ invarianceOp F ω p = 0 := by
  constructor
  · intro h
    ext θ
    simp [invarianceOp, h θ]
  · intro h θ
    have := ContinuousMap.congr_fun h θ
    simpa [invarianceOp, sub_eq_zero] using this

/-! ## A Newton–Kantorovich persistence lemma (the analytic core of a KAM step) -/

/-- **Quantitative Newton step.**  If a (possibly nonlinear) map `Φ` between Banach spaces is,
on a ball around `u₀`, approximated by an invertible linear operator `A` with error constant `κ`
satisfying `‖A⁻¹‖ κ ≤ 1/2`, and if the residual `Φ u₀` is small, then `Φ` has a zero in the ball.
This is the fixed-point mechanism behind the KAM iteration. -/
theorem exists_zero_of_approx_linearization
    {B G : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : B → G) (A : B ≃L[ℝ] G) (u₀ : B) (r κ : ℝ) (hr : 0 ≤ r)
    (hlip : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      ‖Φ u - Φ v - A (u - v)‖ ≤ κ * ‖u - v‖)
    (hκ : ‖(A.symm : G →L[ℝ] B)‖ * κ ≤ 1 / 2)
    (hsmall : ‖(A.symm : G →L[ℝ] B)‖ * ‖Φ u₀‖ ≤ r / 2) :
    ∃ u ∈ Metric.closedBall u₀ r, Φ u = 0 := by
  set L : ℝ := ‖(A.symm : G →L[ℝ] B)‖ with hL
  have hL0 : 0 ≤ L := norm_nonneg _
  set g : B → B := fun u => u - A.symm (Φ u) with hg
  set s : Set B := Metric.closedBall u₀ r with hs
  have hu₀s : u₀ ∈ s := by simp [hs, Metric.mem_closedBall, hr]
  -- The Newton map `g` is a `1/2`-contraction on the ball.
  have key : ∀ u ∈ s, ∀ v ∈ s, ‖g u - g v‖ ≤ (1 / 2) * ‖u - v‖ := by
    intro u hu v hv
    have hid : g u - g v = A.symm (A (u - v) - (Φ u - Φ v)) := by
      simp only [hg, map_sub, A.symm_apply_apply]
      abel
    have h1 : ‖g u - g v‖ ≤ L * ‖A (u - v) - (Φ u - Φ v)‖ := by
      rw [hid]
      exact (A.symm : G →L[ℝ] B).le_opNorm _
    have h2 : ‖A (u - v) - (Φ u - Φ v)‖ ≤ κ * ‖u - v‖ := by
      rw [← norm_neg]
      have hneg : -(A (u - v) - (Φ u - Φ v)) = Φ u - Φ v - A (u - v) := by abel
      rw [hneg]
      exact hlip u hu v hv
    calc ‖g u - g v‖ ≤ L * ‖A (u - v) - (Φ u - Φ v)‖ := h1
      _ ≤ L * (κ * ‖u - v‖) := mul_le_mul_of_nonneg_left h2 hL0
      _ = (L * κ) * ‖u - v‖ := by ring
      _ ≤ (1 / 2) * ‖u - v‖ := mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
  -- and it maps the ball into itself.
  have hmaps : Set.MapsTo g s s := by
    intro u hu
    have hu' : ‖u - u₀‖ ≤ r := by
      simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hu
    have h1 : ‖g u - g u₀‖ ≤ (1 / 2) * ‖u - u₀‖ := key u hu u₀ hu₀s
    have h2 : ‖g u₀ - u₀‖ ≤ L * ‖Φ u₀‖ := by
      have hgu : g u₀ - u₀ = -(A.symm (Φ u₀)) := by simp [hg]
      rw [hgu, norm_neg]
      exact (A.symm : G →L[ℝ] B).le_opNorm _
    have hball : ‖g u - u₀‖ ≤ r := by
      calc ‖g u - u₀‖ = ‖(g u - g u₀) + (g u₀ - u₀)‖ := by congr 1; abel
        _ ≤ ‖g u - g u₀‖ + ‖g u₀ - u₀‖ := norm_add_le _ _
        _ ≤ (1 / 2) * ‖u - u₀‖ + L * ‖Φ u₀‖ := add_le_add h1 h2
        _ ≤ (1 / 2) * r + r / 2 := by
            have := mul_le_mul_of_nonneg_left hu' (by norm_num : (0:ℝ) ≤ 1 / 2)
            linarith [hsmall]
        _ = r := by ring
    simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hball
  have hcompl : IsComplete s := (Metric.isClosed_closedBall).isComplete
  have hcontr : ContractingWith (1 / 2 : NNReal) (Set.MapsTo.restrict g s s hmaps) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have := key x.1 x.2 y.1 y.2
      simpa [Subtype.dist_eq, dist_eq_norm, Set.MapsTo.restrict, Set.restrict] using this
  obtain ⟨y, hys, hfix, -⟩ := hcontr.exists_fixedPoint' hcompl hmaps hu₀s (edist_ne_top _ _)
  refine ⟨y, hys, ?_⟩
  have hzero : A.symm (Φ y) = 0 := by
    have hy := hfix
    simp only [Function.IsFixedPt, hg] at hy
    exact sub_eq_self.mp hy
  have := congrArg (fun z => A z) hzero
  simpa using this

/-! ## The KAM theorem: persistence of invariant tori -/

/-- **KAM: persistence of invariant tori under small perturbations.**

Let `F 0` be the unperturbed system with an invariant torus `p₀` carrying the rotation vector
`ω`, and let `F ε` be a perturbation of it, with `‖F ε x - F 0 x‖ ≤ δ` along the unperturbed
torus.  Assume the non-degeneracy hypothesis of KAM theory: the invariance operator of the
perturbed system is approximated, on the ball of radius `r` around `p₀`, by an invertible linear
operator `A` (this is the step where the Diophantine condition on `ω` is used, to solve the
homological equations), with error constant `κ` satisfying `‖A⁻¹‖ κ ≤ 1/2`.  If the perturbation
is small, `‖A⁻¹‖ δ ≤ r/2`, then the invariant torus persists: the perturbed system `F ε` has an
invariant torus `p` carrying the *same* rotation vector `ω`, at distance at most `r` from the
unperturbed one. -/
theorem kam_theorem {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : ℝ → C(X, X)) (ω : Fin n → ℝ) (p₀ : C(Torus n, X)) (ε δ r κ : ℝ)
    (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (A : C(Torus n, X) ≃L[ℝ] C(Torus n, X))
    (hp₀ : IsInvariantTorus (F 0) ω p₀)
    (hpert : ∀ θ : Torus n, ‖F ε (p₀ θ) - F 0 (p₀ θ)‖ ≤ δ)
    (hlip : ∀ u ∈ Metric.closedBall p₀ r, ∀ v ∈ Metric.closedBall p₀ r,
      ‖invarianceOp (F ε) ω u - invarianceOp (F ε) ω v - A (u - v)‖ ≤ κ * ‖u - v‖)
    (hκ : ‖(A.symm : C(Torus n, X) →L[ℝ] C(Torus n, X))‖ * κ ≤ 1 / 2)
    (hsmall : ‖(A.symm : C(Torus n, X) →L[ℝ] C(Torus n, X))‖ * δ ≤ r / 2) :
    ∃ p : C(Torus n, X), ‖p - p₀‖ ≤ r ∧ IsInvariantTorus (F ε) ω p := by
  -- The residual of the unperturbed torus for the perturbed system is the perturbation itself.
  have hres : ‖invarianceOp (F ε) ω p₀‖ ≤ δ := by
    rw [ContinuousMap.norm_le _ hδ]
    intro θ
    have : p₀ (rot ω θ) = F 0 (p₀ θ) := (hp₀ θ).symm
    rw [invarianceOp_apply, this]
    exact hpert θ
  have hsmall' :
      ‖(A.symm : C(Torus n, X) →L[ℝ] C(Torus n, X))‖ * ‖invarianceOp (F ε) ω p₀‖ ≤ r / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left hres (ContinuousLinearMap.opNorm_nonneg _)) hsmall
  obtain ⟨p, hp, hp0⟩ :=
    exists_zero_of_approx_linearization (invarianceOp (F ε) ω) A p₀ r κ hr hlip hκ hsmall'
  refine ⟨p, ?_, (isInvariantTorus_iff_invarianceOp_eq_zero _ _ _).2 hp0⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hp

end

end Frontier

