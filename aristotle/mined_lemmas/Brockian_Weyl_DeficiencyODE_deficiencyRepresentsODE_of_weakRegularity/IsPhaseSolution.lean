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
