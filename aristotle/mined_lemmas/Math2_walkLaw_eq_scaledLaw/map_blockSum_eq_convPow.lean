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

theorem map_blockSum_eq_convPow (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (p q : ℕ) :
    P.map (fun ω => ∑ i ∈ Finset.Ico p q, X i ω) = convPow μ (q - p) := by
  have hshift : Function.Injective (fun i : ℕ => p + i) := fun i j hij =>
    Nat.add_left_cancel hij
  have hindep' : iIndepFun (fun i : ℕ => X (p + i)) P := hindep.precomp hshift
  have hident' : ∀ i, P.map (X (p + i)) = μ := fun i => hident _
  have hsum : (fun ω => ∑ i ∈ Finset.Ico p q, X i ω)
      = fun ω => ∑ i ∈ Finset.range (q - p), X (p + i) ω := by
    funext ω
    exact Finset.sum_Ico_eq_sum_range (fun i => X i ω) p q
  rw [hsum]
  exact map_partialSum_eq_convPow (fun i => hmeas (p + i)) hindep' hident' (q - p)

/-- Measurability of the block sums. -/
