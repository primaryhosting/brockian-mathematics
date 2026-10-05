import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₄` (vertices indexed cyclically by `Fin 4`:
`i` is adjacent to `i + 1` and `i - 1`). -/

lemma two_cos_two_pi_k_div_four (k : Fin 4) :
    2 * Real.cos (2 * Real.pi * k / 4) = ![2, 0, -2, 0] k := by
  fin_cases k
  · norm_num
  · norm_num [show 2 * Real.pi / 4 = Real.pi / 2 by ring]
  · norm_num [show 2 * Real.pi * 2 / 4 = Real.pi by ring]
  · norm_num [show 2 * Real.pi * 3 / 4 = Real.pi + Real.pi / 2 by ring, Real.cos_add]

/-- **Hückel theory for cyclobutadiene (C₄).**  A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₄` if and only if `μ = 2·cos(2πk/4)` for some
`k ∈ {0, 1, 2, 3}` (i.e. `μ ∈ {2, 0, -2}`, the Hückel π-levels `α + 2β, α, α, α - 2β`). -/
