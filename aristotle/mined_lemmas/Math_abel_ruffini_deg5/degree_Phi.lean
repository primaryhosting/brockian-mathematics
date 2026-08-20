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

theorem degree_Phi : (Phi R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [Phi, degree_add_eq_left_of_degree_lt]
    convert (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by simp))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by simp))

