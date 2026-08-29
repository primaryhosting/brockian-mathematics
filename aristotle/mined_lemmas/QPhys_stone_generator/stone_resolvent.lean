import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Topology Complex
open scoped LinearPMap

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U : ℝ → (H →L[ℂ] H)` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, each `U t` norm
preserving (hence unitary, since the group law provides the inverse `U (-t)`), and such that
`t ↦ U t x` is continuous for every `x` (strong continuity). -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => U t x

omit [CompleteSpace H] in
/-- Sanity check that the hypotheses are satisfiable: the constant family `U t = 1` is a
strongly continuous one-parameter unitary group. -/

theorem stone_resolvent {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (y : H) :
    ∃ x : H, HasDerivAt (fun t : ℝ => U t x) (x - y) 0 := by
  classical
  set g : ℝ → H := fun s => (Real.exp (-s) : ℂ) • U s y with hgdef
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul
      (hU.continuous_apply y)
  have hgnorm : ∀ s, ‖g s‖ = Real.exp (-s) * ‖y‖ := by
    intro s
    simp [hgdef, norm_smul, hU.norm_map, Complex.norm_exp]
  have hInt : ∀ c : ℝ, IntegrableOn g (Set.Ioi c) := by
    intro c
    have hbound : IntegrableOn (fun s : ℝ => Real.exp (-s) * ‖y‖) (Set.Ioi c) := by
      have := (exp_neg_integrableOn_Ioi c (b := 1) one_pos).mul_const ‖y‖
      simpa using this
    refine Integrable.mono' hbound hgc.aestronglyMeasurable ?_
    filter_upwards with s using le_of_eq (hgnorm s)
  have hIntervalInt : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgc.intervalIntegrable a b
  set R : H := ∫ s in Set.Ioi (0 : ℝ), g s with hR
  have hg0 : g 0 = y := by simp [hgdef, hU.map_zero]
  have hkey : ∀ t : ℝ, U t R = (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R) := by
    intro t
    have h1 : U t R = ∫ s in Set.Ioi (0 : ℝ), U t (g s) :=
      (ContinuousLinearMap.integral_comp_comm (U t) (hInt 0)).symm
    have h2 : ∀ s : ℝ, U t (g s) = (Real.exp t : ℂ) • g (t + s) := by
      intro s
      have hUts : U (t + s) y = U t (U s y) := by
        rw [hU.map_add]; rfl
      simp only [hgdef, map_smul, hUts, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
      ring_nf
    have htrans : (∫ s in Set.Ioi (0 : ℝ), g (t + s)) = ∫ s in Set.Ioi t, g s := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) t).setIntegral_preimage_emb
        (measurableEmbedding_addLeft t) g (Set.Ioi t)
      simpa using h
    calc U t R = ∫ s in Set.Ioi (0 : ℝ), U t (g s) := h1
      _ = ∫ s in Set.Ioi (0 : ℝ), (Real.exp t : ℂ) • g (t + s) := by simp_rw [h2]
      _ = (Real.exp t : ℂ) • ∫ s in Set.Ioi (0 : ℝ), g (t + s) := integral_smul _ _
      _ = (Real.exp t : ℂ) • ∫ s in Set.Ioi t, g s := by rw [htrans]
      _ = (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R) := by
          rw [intervalIntegral.integral_interval_add_Ioi (hInt t) (hInt 0)]
  refine ⟨R, ?_⟩
  have hexp : HasDerivAt (fun t : ℝ => ((Real.exp t : ℝ) : ℂ)) 1 0 := by
    have := (Real.hasDerivAt_exp 0).ofReal_comp
    simpa using this
  have hphi : HasDerivAt (fun t : ℝ => ∫ s in t..(0 : ℝ), g s) (-g 0) 0 :=
    intervalIntegral.integral_hasDerivAt_left (hIntervalInt 0 0)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  have hderiv : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R))
      (R - y) 0 := by
    have h := hexp.smul (hphi.add_const R)
    convert h using 1
    simp [hg0, sub_eq_neg_add]
  have hfun : (fun t : ℝ => U t R)
      = fun t : ℝ => (Real.exp t : ℂ) • ((∫ s in t..(0 : ℝ), g s) + R) := funext hkey
  rw [hfun]
  exact hderiv

