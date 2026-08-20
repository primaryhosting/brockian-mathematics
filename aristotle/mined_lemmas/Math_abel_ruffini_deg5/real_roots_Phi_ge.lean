/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`, so the header
-- above is a plain comment and is repeated verbatim as a module docstring after the import.)

/-
The argument below is the classical Galois-theoretic proof of the Abel-Ruffini theorem
in degree 5, following the treatment of `Archive/Wiedijk100Theorems/AbelRuffini.lean`
in mathlib4 (author: Thomas Browning, Apache 2.0).  It is reproduced here in
self-contained form because the mathlib `Archive` library is not imported by default.

The key mathlib ingredients are:
* `solvableByRad.isSolvable'`  (an irreducible polynomial with a root solvable by radicals
  has solvable Galois group);
* `Polynomial.Gal.galActionHom_bijective_of_prime_degree'`  (an irreducible polynomial of
  prime degree with 1-3 non-real roots has full Galois group);
* `Equiv.Perm.not_solvable`  (the symmetric group on 5 letters is not solvable).
-/

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

namespace AbelRuffiniQuintic

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`. -/

theorem real_roots_Phi_ge (hab : b < a) : 2 ≤ Fintype.card ((Phi ℚ a b).rootSet ℝ) := by
  have q_ne_zero : Phi ℚ a b ≠ 0 := (monic_Phi a b).ne_zero
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_Phi_ge_aux a b hab
  have key : ↑({x, y} : Finset ℝ) ⊆ (Phi ℚ a b).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
  convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

