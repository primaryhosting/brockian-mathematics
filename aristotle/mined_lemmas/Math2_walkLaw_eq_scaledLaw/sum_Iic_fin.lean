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

theorem sum_Iic_fin (k : ℕ) (j : Fin k) (g : ℕ → ℝ) :
    ∑ l ∈ Finset.Iic j, g (l : ℕ) = ∑ l ∈ Finset.range ((j : ℕ) + 1), g l := by
  refine Finset.sum_nbij' (i := fun l : Fin k => (l : ℕ))
    (j := fun l : ℕ => (⟨min l (j : ℕ), lt_of_le_of_lt (min_le_right _ _) j.isLt⟩ : Fin k))
    ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_Iic] at hl
    simp only [Finset.mem_range]
    have : (l : ℕ) ≤ (j : ℕ) := hl
    omega
  · intro l _
    simp only [Finset.mem_Iic]
    show min l (j : ℕ) ≤ (j : ℕ)
    omega
  · intro l hl
    simp only [Finset.mem_Iic] at hl
    have : (l : ℕ) ≤ (j : ℕ) := hl
    ext
    show min (l : ℕ) (j : ℕ) = (l : ℕ)
    omega
  · intro l hl
    simp only [Finset.mem_range] at hl
    show min l (j : ℕ) = l
    omega
  · intro l _
    rfl


/-- If `s ≤ u` are nonnegative times, the number of steps in the block between them, divided by
`n`, converges to `u - s`. -/
