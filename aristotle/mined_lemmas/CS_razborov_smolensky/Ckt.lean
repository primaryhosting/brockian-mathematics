import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def Ckt.depth {n : ℕ} : ∀ {k : ℕ}, Ckt n k → Fin k → ℕ
  | _, .nil => Fin.elim0
  | _, .cons c g => Fin.snoc (Ckt.depth c) (g.depth (Ckt.depth c))

/-- The class `AC⁰[q]`: families of Boolean functions computed by polynomial size,
constant depth circuits with unbounded fan-in `AND`, `OR` and `MOD q` gates. -/
