/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`. -/

lemma negMulLog_concave_pair {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (-(x * Real.log x)) + b * (-(y * Real.log y)) ≤
      -((a * x + b * y) * Real.log (a * x + b * y)) := by
  have h := Real.strictConcaveOn_negMulLog.concaveOn.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy)
    ha hb hab
  simpa only [Real.negMulLog, smul_eq_mul, neg_mul] using h

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave** on the set of nonnegative vectors
(in particular on the probability simplex). -/
