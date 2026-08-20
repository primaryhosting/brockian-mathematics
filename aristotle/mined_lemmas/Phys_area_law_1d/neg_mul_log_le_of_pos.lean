/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Real Finset

namespace Phys

/-- Pointwise bound on the entropy contribution `-x log x` of a weight `x ≥ 0`
in terms of *any* positive comparison value `q`:
`-x log x = x log (1/q) + x log (q/x) ≤ x (-log q) + (q - x) ≤ x (-log q) + q`,
using `log t ≤ t - 1`. -/

theorem neg_mul_log_le_of_pos {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    -(x * Real.log x) ≤ x * (-Real.log q) + q := by
  rcases eq_or_lt_of_le hx with h | hx0
  · simp [← h, le_of_lt hq]
  · have hlog : Real.log (q / x) ≤ q / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (q / x) = Real.log q - Real.log x :=
      Real.log_div (ne_of_gt hq) (ne_of_gt hx0)
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    rw [h2] at hmul
    have hx' : x * (q / x - 1) = q - x := by field_simp
    rw [hx'] at hmul
    nlinarith

/-- **Entanglement-entropy area law in one dimension** (the entropy-bound content of
Hastings' theorem).

Physical setting: a pure state of a 1D spin chain is cut into a left and a right half.
Writing the Schmidt decomposition across the cut, `p i` denotes the squared Schmidt
coefficients (equivalently, the eigenvalues of the reduced density matrix of the left
half), so `p` is a probability vector of length `n`, where `n` grows with the system
size, and the entanglement entropy across the cut is the Shannon entropy
`S = -∑ i, p i * log (p i)`.

The physical input coming from the spectral gap — which we take here as the hypothesis
`hdecay` — is that a gapped ground state is approximated across the cut by a matrix
product state, so that the Schmidt spectrum decays exponentially:
`p i ≤ C * exp (-α * i)` with `C, α > 0` fixed by the gap and the interaction range,
independent of the system size.

Conclusion: the entanglement entropy is bounded by an explicit constant depending only
on `C` and `α` — in particular **independent of the number `n` of Schmidt coefficients,
i.e. of the length of the chain**. This "constant, not extensive" bound is precisely the
1D area law (the boundary of an interval is a single point, so the "area" is `O(1)`).

The proof: apply `neg_mul_log_le_of_pos` with comparison value `q i = C * exp (-α * i)`,
which gives `-p i log (p i) ≤ p i * (α i - log C) + C e^{-α i}`; summing, `∑ p i = 1`
handles the `-log C` term, the hypothesis `hdecay` bounds `∑ i * p i` by
`C ∑ i e^{-α i}`, and both geometric-type series are summed in closed form. -/
