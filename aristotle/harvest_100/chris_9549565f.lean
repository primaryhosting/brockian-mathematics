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

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity** of a potential `q : ℝ → ℂ`: `q` is bounded on every compact interval.
This is much weaker than continuity of `q`; it is exactly what is needed to run the Gronwall
argument behind uniqueness for the Sturm–Liouville system. -/
def WeaklyRegular (q : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ‖q t‖ ≤ C

/-- `IsSolution q z w` says that `w = (u, u')` is a solution of the first-order system
associated with the Sturm–Liouville equation `-u'' + q u = z u`, i.e.
`u' = w.2` and `w.2' = (q - z) u`. -/
def IsSolution (q : ℝ → ℂ) (z : ℂ) (w : ℝ → ℂ × ℂ) : Prop :=
  ∀ t : ℝ, HasDerivAt w ((w t).2, (q t - z) * (w t).1) t

/-- The space of solutions of the Sturm–Liouville system, as a `ℂ`-submodule of
vector-valued functions. -/
def solutionSpace (q : ℝ → ℂ) (z : ℂ) : Submodule ℂ (ℝ → ℂ × ℂ) where
  carrier := {w | IsSolution q z w}
  add_mem' := by
    intro w₁ w₂ h₁ h₂ t
    have := (h₁ t).add (h₂ t)
    convert this using 1
    simp [Prod.ext_iff]
    ring
  zero_mem' := by
    intro t
    simpa using (hasDerivAt_const t (0 : ℂ × ℂ))
  smul_mem' := by
    intro c w h t
    have := (h t).const_smul c
    convert this using 1
    simp [Prod.ext_iff, Prod.smul_def]
    ring

/-- The **deficiency space** of the Sturm–Liouville expression at the spectral parameter `z`,
on the half line `(0, ∞)`: the solutions of the ODE whose first component is square integrable.
By Weyl's theory this is the space representing `ker (T* - z)` for the minimal operator `T`. -/
def deficiencySpace (q : ℝ → ℂ) (z : ℂ) : Submodule ℂ (ℝ → ℂ × ℂ) where
  carrier := {w | IsSolution q z w ∧ MemLp (fun t => (w t).1) 2 (volume.restrict (Set.Ioi 0))}
  add_mem' := by
    rintro w₁ w₂ ⟨hs₁, hL₁⟩ ⟨hs₂, hL₂⟩
    exact ⟨(solutionSpace q z).add_mem hs₁ hs₂, by simpa using hL₁.add hL₂⟩
  zero_mem' := ⟨(solutionSpace q z).zero_mem, by simp⟩
  smul_mem' := by
    rintro c w ⟨hs, hL⟩
    exact ⟨(solutionSpace q z).smul_mem c hs, by simpa using hL.const_smul c⟩

/-- Evaluation of a deficiency element at the base point `0`, recording the Cauchy data
`(u 0, u' 0)` of the underlying ODE solution. -/
def evalAt0 (q : ℝ → ℂ) (z : ℂ) : deficiencySpace q z →ₗ[ℂ] ℂ × ℂ where
  toFun w := (w : ℝ → ℂ × ℂ) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Uniqueness

variable {q : ℝ → ℂ} {z : ℂ}

/-- The vector field of the Sturm–Liouville system. -/
private def sturmField (q : ℝ → ℂ) (z : ℂ) : ℝ → (ℂ × ℂ) → (ℂ × ℂ) :=
  fun t x => (x.2, (q t - z) * x.1)

private theorem lipschitz_sturmField {R C : ℝ} (hC : ∀ t ∈ Set.Icc (-R) R, ‖q t‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc (-R) R) :
    LipschitzOnWith (Real.toNNReal (max 1 (C + ‖z‖))) (sturmField q z t) Set.univ := by
  have hCnn : (0:ℝ) ≤ max 1 (C + ‖z‖) := le_trans zero_le_one (le_max_left _ _)
  have hqz : ‖q t - z‖ ≤ max 1 (C + ‖z‖) := by
    refine le_trans (le_trans (norm_sub_le _ _) ?_) (le_max_right _ _)
    have := hC t ht
    linarith
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x _ y _
  have hx : dist (sturmField q z t x) (sturmField q z t y)
      = max (dist x.2 y.2) (‖q t - z‖ * dist x.1 y.1) := by
    simp [sturmField, dist_eq_norm, ← mul_sub]
  rw [hx, Real.coe_toNNReal _ hCnn]
  have h1 : dist x.2 y.2 ≤ max 1 (C + ‖z‖) * dist x y := by
    calc dist x.2 y.2 ≤ dist x y := le_max_right _ _
      _ ≤ max 1 (C + ‖z‖) * dist x y := by
          nlinarith [dist_nonneg (x := x) (y := y), le_max_left 1 (C + ‖z‖)]
  have h2 : ‖q t - z‖ * dist x.1 y.1 ≤ max 1 (C + ‖z‖) * dist x y := by
    have hd : dist x.1 y.1 ≤ dist x y := le_max_left _ _
    have h0 : (0:ℝ) ≤ ‖q t - z‖ := norm_nonneg _
    nlinarith [dist_nonneg (x := x.1) (y := y.1), dist_nonneg (x := x) (y := y)]
  exact max_le h1 h2

/-- Uniqueness of solutions of the Sturm–Liouville system with vanishing Cauchy data:
a weakly regular potential forces a solution vanishing at `0` to vanish identically. -/
theorem eq_zero_of_isSolution_of_apply_zero (hq : WeaklyRegular q) {w : ℝ → ℂ × ℂ}
    (hw : IsSolution q z w) (h0 : w 0 = 0) : w = 0 := by
  funext t
  obtain ⟨R, hRt, hR0⟩ : ∃ R : ℝ, |t| < R ∧ (0:ℝ) < R :=
    ⟨|t| + 1, by linarith, by positivity⟩
  obtain ⟨C, hC⟩ := hq (-R) R
  have hmem : t ∈ Set.Icc (-R) R := by
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  have key : Set.EqOn w 0 (Set.Icc (-R) R) := by
    refine ODE_solution_unique_of_mem_Icc (v := sturmField q z) (s := fun _ => Set.univ)
      (K := Real.toNNReal (max 1 (C + ‖z‖))) (t₀ := 0)
      (fun s hs => lipschitz_sturmField hC (Set.mem_Icc_of_Ioo hs))
      ⟨by linarith, hR0⟩
      (fun s _ => (hw s).continuousAt.continuousWithinAt)
      (fun s _ => hw s) (fun _ _ => Set.mem_univ _)
      continuousOn_const
      (fun s _ => by simpa [sturmField] using (hasDerivAt_const s (0 : ℂ × ℂ)))
      (fun _ _ => Set.mem_univ _) (by simpa using h0)
  simpa using key hmem

end Uniqueness

/-- **Deficiency represents the ODE, for weakly regular potentials.**

For a potential `q` bounded on compact intervals (weak regularity) and any spectral parameter
`z : ℂ`, every element of the deficiency space of the Sturm–Liouville expression
`-u'' + q u = z u` on the half line is faithfully represented by its Cauchy data
`(u 0, u' 0) ∈ ℂ²`; consequently the deficiency space has rank at most `2`.

No hypothesis beyond weak regularity of `q` is assumed. -/
theorem deficiencyRepresentsODE_of_weakRegularity (q : ℝ → ℂ) (z : ℂ) (hq : WeaklyRegular q) :
    Function.Injective (evalAt0 q z) ∧ Module.rank ℂ (deficiencySpace q z) ≤ 2 := by
  have hinj : Function.Injective (evalAt0 q z) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨w, hw, hL⟩ h
    have h0 : w 0 = 0 := h
    exact Subtype.ext (eq_zero_of_isSolution_of_apply_zero (z := z) hq hw h0)
  refine ⟨hinj, ?_⟩
  have hr : Module.rank ℂ (deficiencySpace q z) ≤ Module.rank ℂ (ℂ × ℂ) :=
    (evalAt0 q z).rank_le_of_injective hinj
  simpa [show (1 : Cardinal) + 1 = 2 from one_add_one_eq_two] using hr

end Brockian.Weyl.DeficiencyODE

#print axioms Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity

