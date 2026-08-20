/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

lemma finite_setOf_pow_eq {k : ℕ} (hk : 0 < k) (c : ℚ) : {x : ℚ | x ^ k = c}.Finite := by
  have hp : (Polynomial.X ^ k - Polynomial.C c : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hk c
  refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hp) ?_
  intro x hx
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  simp only [Set.mem_setOf_eq] at hx
  rw [hx, sub_self]

end Auxiliary

/-- **Reduction step.**  If the Fermat curve of degree `m` has finitely many rational
points, then so does the Fermat curve of degree `n` for every multiple `n` of `m`: the map
`(x, y) ↦ (x ^ k, y ^ k)` with `n = m * k` sends the rational points of the degree-`n` curve
to those of the degree-`m` curve with finite fibres. -/
