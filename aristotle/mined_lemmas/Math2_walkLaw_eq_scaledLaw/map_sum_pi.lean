import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem map_sum_pi (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).map (fun ω => ∑ i, ω i) = convPow μ N := by
  induction N with
  | zero =>
      simp [convPow_zero, Measure.map_const]
  | succ N ih =>
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with he
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0
      have hcomp : (fun ω : Fin (N + 1) → ℝ => ∑ i, ω i)
          = (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) ∘ e := by
        funext ω
        simp [he, MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ, Fin.tail]
      have hmeas : Measurable (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) := by fun_prop
      calc (Measure.pi (fun _ : Fin (N + 1) => μ)).map (fun ω => ∑ i, ω i)
          = ((Measure.pi (fun _ : Fin (N + 1) => μ)).map e).map
              (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) := by
            rw [hcomp, ← Measure.map_map hmeas e.measurable]
        _ = (μ.prod (Measure.pi (fun _ : Fin N => μ))).map
              (fun p : ℝ × (Fin N → ℝ) => p.1 + ∑ j, p.2 j) := by rw [hmp.map_eq]
        _ = μ ∗ convPow μ N := by
            have key := Measure.map_prod_map (f := (id : ℝ → ℝ))
              (g := fun ω : Fin N → ℝ => ∑ i, ω i) μ (Measure.pi (fun _ : Fin N => μ))
              measurable_id (by fun_prop)
            rw [Measure.map_id] at key
            rw [Measure.conv, ← ih, key, Measure.map_map (by fun_prop) (by fun_prop)]
            simp [Function.comp_def, Prod.map]
        _ = convPow μ (N + 1) := by rw [convPow_succ, Measure.conv_comm]

/-- **The law of a random walk with i.i.d. steps.**  If `X` is an independent family of random
variables, each with law `μ`, then the partial sum `X 0 + ⋯ + X (m-1)` has law `convPow μ m`. -/
