/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the 5-cycle `C₅`

The Hückel secular problem for the cyclic polyene `C₅H₅` reduces (after removing the
Coulomb integral `α` and dividing by the resonance integral `β`) to the eigenvalue
problem for the adjacency matrix of the cycle graph `C₅`.

The main result `Chem.huckel_C5` states that the eigenvalues of that adjacency matrix
are exactly the five numbers `2 * cos (2 * π * k / 5)`, `k = 0, 1, 2, 3, 4`
(equivalently `2`, `(√5 - 1)/2` twice and `-(√5 + 1)/2` twice).
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where `α = 0`, `β = 1`). -/

private lemma cos_two_pi_two_div_five : Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 5)
    = -(1 + Real.sqrt 5) / 4 := by
  have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 5 = Real.pi - Real.pi / 5 := by push_cast; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

end Auxiliary

/-- **Hückel eigenvalues of `C₅`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₅` if and only if `μ = 2 cos (2πk/5)` for some
`k ∈ {0, 1, 2, 3, 4}`. -/
