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

theorem map_partialSum_eq_convPow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hident : ∀ i, P.map (X i) = μ) (m : ℕ) :
    P.map (fun ω => ∑ i ∈ Finset.range m, X i ω) = convPow μ m := by
  have hinj : Function.Injective (fun i : Fin m => (i : ℕ)) := Fin.val_injective
  have hindep' : iIndepFun (fun i : Fin m => X (i : ℕ)) P := hindep.precomp hinj
  have hvec : P.map (fun ω (i : Fin m) => X (i : ℕ) ω)
      = Measure.pi (fun _ : Fin m => μ) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin m => (hmeas (i : ℕ)).aemeasurable)).1 hindep']
    exact congrArg Measure.pi (funext fun i => hident (i : ℕ))
  have hsum : (fun ω => ∑ i ∈ Finset.range m, X i ω)
      = (fun v : Fin m → ℝ => ∑ i, v i) ∘ (fun ω (i : Fin m) => X (i : ℕ) ω) := by
    funext ω
    exact (Fin.sum_univ_eq_sum_range (fun i => X i ω) m).symm
  rw [hsum, ← Measure.map_map (by fun_prop) (by fun_prop), hvec, map_sum_pi]

end Math2

import RequestProject.Taylor

/-!
# Smooth step functions

We construct, for every `x : ℝ` and `δ > 0`, a smooth test function which equals `1` on
`Iic x`, vanishes on `Ici (x + δ)` and takes values in `[0, 1]`.  These functions are used to
sandwich indicators of half lines between smooth test functions, and hence to upgrade
convergence of integrals of smooth test functions to convergence of distribution functions.
-/

namespace Math2

open Set Filter Topology

/-- The smooth transition function of Mathlib. -/
