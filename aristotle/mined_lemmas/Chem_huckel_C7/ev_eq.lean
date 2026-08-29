/- (Lean requires `import` to precede any module docstring `/-! ... -/`, so this header
is given as a plain block comment.)
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex Real

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `Fin 7`
(where addition is modulo `7`): vertices `i` and `j` are adjacent iff they differ by one
step around the cycle. -/

lemma ev_eq (k : Fin 7) : ((ev k : ℝ) : ℂ) = w ^ (k : ℕ) + (w ^ (k : ℕ))⁻¹ := by
  have h : w ^ (k : ℕ) = Complex.exp (((2 * π * (k : ℕ) / 7 : ℝ) : ℂ) * I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, ← Complex.exp_neg, ev]
  push_cast
  rw [Complex.two_cos]
  ring_nf

