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

theorem map_blockSums_eq_pi (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) {a : ℕ → ℕ} (ha : Monotone a) (k : ℕ) :
    P.map (fun ω (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)
      = Measure.pi (fun j : Fin k => convPow μ (a (j + 1) - a j)) := by
  induction k with
  | zero =>
      have hconst : (fun (ω : Ω) (j : Fin 0) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)
          = fun _ => (fun j : Fin 0 => (0 : ℝ)) := by
        funext ω j
        exact j.elim0
      rw [hconst, Measure.map_const, measure_univ, one_smul]
      exact (Measure.pi_of_empty _ _).symm
  | succ k ih =>
      have hmeas1 : Measurable (fun ω => ∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω) :=
        measurable_blockSum hmeas _ _
      have hmeas2 : Measurable
          (fun (ω : Ω) (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) :=
        measurable_pi_lambda _ fun j => measurable_blockSum hmeas _ _
      have hpair := (indepFun_iff_map_prod_eq_prod_map_map hmeas1.aemeasurable
        hmeas2.aemeasurable).1 (indepFun_blockSum_vector hmeas hindep ha k)
      rw [map_blockSum_eq_convPow hmeas hindep hident, ih] at hpair
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k) with he
      have hmp := measurePreserving_piFinSuccAbove
        (fun j : Fin (k + 1) => convPow μ (a (j + 1) - a j)) (Fin.last k)
      have hsymm : ∀ p : ℝ × (Fin k → ℝ),
          (⇑e.symm) p = (Fin.snoc p.2 p.1 : Fin (k + 1) → ℝ) := by
        intro p
        show Fin.insertNth (Fin.last k) p.1 p.2 = (Fin.snoc p.2 p.1 : Fin (k + 1) → ℝ)
        exact Fin.insertNth_last' _ _
      have hcomp : (fun (ω : Ω) (j : Fin (k + 1)) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)
          = (⇑e.symm) ∘ (fun ω => ((∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω),
              fun j : Fin k => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)) := by
        funext ω
        simp only [Function.comp_apply, hsymm]
        funext j
        refine Fin.lastCases ?_ ?_ j
        · simp
        · intro j'
          simp
      have hpairmeas : Measurable (fun ω => ((∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω),
          fun j : Fin k => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω)) := hmeas1.prodMk hmeas2
      rw [hcomp, ← Measure.map_map e.symm.measurable hpairmeas, hpair]
      have := (hmp.symm e).map_eq
      simpa [Fin.succAbove_last] using this

end Blocks

end Math2

import Mathlib

/-!
# Convolution powers

`Math2.convPow μ n` is the `n`-fold convolution power of a measure on `ℝ`; it is the law of the
sum of `n` independent random variables with law `μ`, i.e. of the random walk after `n` steps.
-/

namespace Math2

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The `n`-fold convolution power of a measure on `ℝ`. -/
