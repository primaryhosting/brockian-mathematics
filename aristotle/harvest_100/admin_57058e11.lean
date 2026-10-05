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

import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity of the potential.** The coefficient `q` is bounded on every compact
interval.  This is far weaker than continuity (no measurability, no smoothness); it is exactly
the amount of regularity needed for Weyl's deficiency theory of the Sturm–Liouville expression
`τ u = -u'' + q u`. -/
def WeaklyRegular (q : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ t ∈ Icc a b, ‖q t‖ ≤ C

/-- The phase-space vector field associated with the Sturm–Liouville equation
`-u'' + q u = z u`, i.e. with `u'' = (q - z) u`, written for the pair `Y = (u, u')`. -/
def field (q : ℝ → ℂ) (z : ℂ) (t : ℝ) (Y : ℂ × ℂ) : ℂ × ℂ := (Y.2, (q t - z) * Y.1)

/-- `Y = (u, u')` is a (global) solution of the Sturm–Liouville equation `-u'' + q u = z u`,
written as a first-order system in phase space. -/
def IsPhaseSolution (q : ℝ → ℂ) (z : ℂ) (Y : ℝ → ℂ × ℂ) : Prop :=
  ∀ t, HasDerivAt Y (field q z t (Y t)) t

section Basic

variable {q : ℝ → ℂ} {z : ℂ}

lemma hasDerivAt_fst {f : ℝ → ℂ × ℂ} {w : ℂ × ℂ} {t : ℝ} (h : HasDerivAt f w t) :
    HasDerivAt (fun s => (f s).1) w.1 t :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t h

lemma hasDerivAt_snd {f : ℝ → ℂ × ℂ} {w : ℂ × ℂ} {t : ℝ} (h : HasDerivAt f w t) :
    HasDerivAt (fun s => (f s).2) w.2 t :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t h

/-- A phase-space solution really solves the second-order equation: its first component `u`
is differentiable with derivative the second component, and that second component is
differentiable with derivative `(q - z) u`. -/
lemma IsPhaseSolution.componentwise {Y : ℝ → ℂ × ℂ} (hY : IsPhaseSolution q z Y) (t : ℝ) :
    HasDerivAt (fun s => (Y s).1) ((Y t).2) t ∧
      HasDerivAt (fun s => (Y s).2) ((q t - z) * (Y t).1) t :=
  ⟨hasDerivAt_fst (hY t), hasDerivAt_snd (hY t)⟩

/-- The phase-space field is Lipschitz with any constant dominating both `1` and `‖q t - z‖`. -/
lemma field_lipschitzWith (t : ℝ) {K : NNReal} (h1 : (1 : ℝ) ≤ (K : ℝ))
    (h2 : ‖q t - z‖ ≤ (K : ℝ)) : LipschitzWith K (field q z t) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y W
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hm1 : dist Y.1 W.1 ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := le_max_left _ _
  have hm2 : dist Y.2 W.2 ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := le_max_right _ _
  have hmnn : (0 : ℝ) ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := le_trans dist_nonneg hm1
  have hmul : dist ((q t - z) * Y.1) ((q t - z) * W.1) = ‖q t - z‖ * dist Y.1 W.1 := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [field]
  refine max_le ?_ ?_
  · calc dist Y.2 W.2 ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := hm2
      _ ≤ (K : ℝ) * max (dist Y.1 W.1) (dist Y.2 W.2) := le_mul_of_one_le_left hmnn h1
  · rw [hmul]
    exact mul_le_mul h2 hm1 dist_nonneg hK0

/-- **Uniqueness for the Sturm–Liouville initial value problem** under weak regularity only:
two global phase-space solutions with the same value at one point coincide. -/
theorem IsPhaseSolution.eq_of_eq_at (hq : WeaklyRegular q) {Y W : ℝ → ℂ × ℂ}
    (hY : IsPhaseSolution q z Y) (hW : IsPhaseSolution q z W) {t₀ : ℝ} (h : Y t₀ = W t₀) :
    Y = W := by
  funext t
  set A : ℝ := min t t₀ - 1 with hA
  set B : ℝ := max t t₀ + 1 with hB
  have htA : t ∈ Ioo A B := by
    constructor
    · have : min t t₀ ≤ t := min_le_left _ _
      simp only [hA]; linarith
    · have : t ≤ max t t₀ := le_max_left _ _
      simp only [hB]; linarith
  have ht₀A : t₀ ∈ Ioo A B := by
    constructor
    · have : min t t₀ ≤ t₀ := min_le_right _ _
      simp only [hA]; linarith
    · have : t₀ ≤ max t t₀ := le_max_right _ _
      simp only [hB]; linarith
  obtain ⟨C, hC⟩ := hq A B
  have hAB : A ≤ B := le_of_lt (lt_trans htA.1 htA.2)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (q A)) (hC A ⟨le_rfl, hAB⟩)
  set Kr : ℝ := 1 + C + ‖z‖ with hKr
  have hKr0 : 0 ≤ Kr := by positivity
  set K : NNReal := ⟨Kr, hKr0⟩ with hKdef
  have hKcoe : (K : ℝ) = Kr := rfl
  have h1 : (1 : ℝ) ≤ (K : ℝ) := by
    rw [hKcoe, hKr]
    have := norm_nonneg z
    linarith
  have hv : ∀ s ∈ Ioo A B, LipschitzOnWith K (field q z s) (univ : Set (ℂ × ℂ)) := by
    intro s hs
    rw [lipschitzOnWith_univ]
    refine field_lipschitzWith s h1 ?_
    have hqs : ‖q s‖ ≤ C := hC s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hsub : ‖q s - z‖ ≤ ‖q s‖ + ‖z‖ := norm_sub_le _ _
    rw [hKcoe, hKr]
    linarith
  have key : EqOn Y W (Ioo A B) :=
    ODE_solution_unique_of_mem_Ioo (s := fun _ => (univ : Set (ℂ × ℂ))) hv ht₀A
      (fun s _ => ⟨hY s, mem_univ _⟩) (fun s _ => ⟨hW s, mem_univ _⟩) h
  exact key htA

end Basic

/-- The **deficiency space** of the Sturm–Liouville expression `-u'' + q u` at the spectral
parameter `z`, relative to the measure `μ`: the space of phase-space solutions `Y = (u, u')`
of `-u'' + q u = z u` whose first component `u` lies in `L²(μ)`.  (For `μ` the Lebesgue measure
restricted to a half line this is Weyl's deficiency space, whose dimension is the deficiency
index of the minimal operator.) -/
def deficiencySubmodule (q : ℝ → ℂ) (z : ℂ) (μ : Measure ℝ) : Submodule ℂ (ℝ → ℂ × ℂ) where
  carrier := {Y | IsPhaseSolution q z Y ∧ MemLp (fun t => (Y t).1) 2 μ}
  add_mem' := by
    rintro Y W ⟨hY, hY2⟩ ⟨hW, hW2⟩
    refine ⟨fun t => ?_, ?_⟩
    · have h := (hY t).add (hW t)
      refine h.congr_deriv ?_
      simp only [field, Pi.add_apply, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
      rw [mul_add]
    · exact hY2.add hW2
  zero_mem' := by
    refine ⟨fun t => ?_, ?_⟩
    · have h : HasDerivAt (fun _ : ℝ => (0 : ℂ × ℂ)) 0 t := hasDerivAt_const t 0
      refine h.congr_deriv ?_
      simp [field, Prod.ext_iff]
    · simp
  smul_mem' := by
    rintro c Y ⟨hY, hY2⟩
    refine ⟨fun t => ?_, ?_⟩
    · have h := (hY t).const_smul c
      refine h.congr_deriv ?_
      simp only [field, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul]
      ring_nf
    · exact hY2.const_smul c

/-- Evaluation of a deficiency element at a point `t₀`, i.e. taking the initial data
`(u t₀, u' t₀)` of the solution. -/
def deficiencyEval (q : ℝ → ℂ) (z : ℂ) (μ : Measure ℝ) (t₀ : ℝ) :
    deficiencySubmodule q z μ →ₗ[ℂ] ℂ × ℂ where
  toFun Y := (Y : ℝ → ℂ × ℂ) t₀
  map_add' := by intro Y W; rfl
  map_smul' := by intro c Y; rfl

/-- **Deficiency represents the ODE (under weak regularity only).**

Let `q : ℝ → ℂ` be weakly regular (bounded on compact intervals — no continuity, smoothness or
measurability is assumed) and let `z : ℂ`.  Then, for the deficiency space at `z` relative to any
measure `μ`:

1. every element of the deficiency space is genuinely a solution of the Sturm–Liouville
   differential equation `-u'' + q u = z u`, its two components being `u` and `u'`;
2. an element of the deficiency space is uniquely determined by its initial data
   `(u t₀, u' t₀)` at any point `t₀`, i.e. the deficiency space is faithfully represented
   inside the two-dimensional space of initial data of the ODE;
3. consequently the deficiency space is finite-dimensional and the deficiency index is at most
   the order `2` of the differential expression. -/
theorem deficiencyRepresentsODE_of_weakRegularity
    (q : ℝ → ℂ) (z : ℂ) (μ : Measure ℝ) (t₀ : ℝ) (hq : WeaklyRegular q) :
    (∀ Y ∈ deficiencySubmodule q z μ, ∀ t : ℝ,
        HasDerivAt (fun s => (Y s).1) ((Y t).2) t ∧
        HasDerivAt (fun s => (Y s).2) ((q t - z) * (Y t).1) t) ∧
      Function.Injective (deficiencyEval q z μ t₀) ∧
      FiniteDimensional ℂ (deficiencySubmodule q z μ) ∧
      Module.finrank ℂ (deficiencySubmodule q z μ) ≤ 2 := by
  have hinj : Function.Injective (deficiencyEval q z μ t₀) := by
    intro Y W h
    have hY : IsPhaseSolution q z (Y : ℝ → ℂ × ℂ) := Y.2.1
    have hW : IsPhaseSolution q z (W : ℝ → ℂ × ℂ) := W.2.1
    exact Subtype.ext (hY.eq_of_eq_at hq hW (t₀ := t₀) h)
  have hfd : FiniteDimensional ℂ (deficiencySubmodule q z μ) :=
    FiniteDimensional.of_injective (deficiencyEval q z μ t₀) hinj
  refine ⟨fun Y hY t => (hY.1).componentwise t, hinj, hfd, ?_⟩
  have hle : Module.finrank ℂ (deficiencySubmodule q z μ) ≤ Module.finrank ℂ (ℂ × ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  simpa using hle

end Brockian.Weyl.DeficiencyODE

