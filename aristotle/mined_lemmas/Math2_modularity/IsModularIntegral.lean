/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the required
-- header appears above as a block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open CongruenceSubgroup

namespace Math2

/-- The number of points of the reduction mod `p` of an integral Weierstrass curve,
counted on the affine model together with the point at infinity. -/

def IsModularIntegral (E : WeierstrassCurve ℤ) : Prop :=
  ∃ (N : ℕ) (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
    0 < N ∧
    qcoeff f 1 = 1 ∧
    (∀ m n : ℕ, Nat.Coprime m n → qcoeff f (m * n) = qcoeff f m * qcoeff f n) ∧
    (∀ p r : ℕ, p.Prime → qcoeff f (p ^ (r + 2)) =
      qcoeff f p * qcoeff f (p ^ (r + 1)) - (if p ∣ N then 0 else (p : ℂ)) * qcoeff f (p ^ r)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ¬ (p : ℤ) ∣ E.Δ → qcoeff f p = (ap E p : ℂ))

/-- Modularity of an elliptic curve over `ℚ`, given by a Weierstrass model with rational
coefficients: some integral Weierstrass model in its `ℚ`-isomorphism class is modular in the
sense of `Math2.IsModularIntegral`. -/
