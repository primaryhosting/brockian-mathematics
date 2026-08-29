/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/

theorem le_margB (hp0 : ∀ x, 0 ≤ p x) (a : A) (b : B) (c : C) : p (a, b, c) ≤ margB p b :=
  le_trans (le_margAB p hp0 a b c) <| Finset.single_le_sum (f := fun a => margAB p (a, b))
    (fun _ _ => Finset.sum_nonneg fun _ _ => hp0 _) (mem_univ a)

omit [Fintype A] [Fintype B] in
