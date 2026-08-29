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

lemma exists_int_of_den_dvd (q : ℚ) (d k : ℕ) (hd : q.den ∣ d) (hk : 1 ≤ k) :
    ∃ m : ℤ, (m : ℚ) = (d : ℚ) ^ k * q := by
  obtain ⟨c, hc⟩ : (q.den : ℕ) ∣ d ^ k := dvd_pow hd (by omega)
  refine ⟨(c : ℤ) * q.num, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have : ((d : ℚ)) ^ k = (q.den : ℚ) * (c : ℚ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hc
  rw [this]
  push_cast
  rw [mul_comm (q.den : ℚ) (c : ℚ), mul_assoc]
  congr 1
  rw [mul_comm]
  exact_mod_cast (Rat.mul_den_eq_num q).symm

/-- A short Weierstrass model over `ℚ` whose coefficients are cleared of denominators comes
from an integral short Weierstrass model. -/
