import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankenyEllipsoidAsPreimage (n q : ℝ) : Set E3 :=
  ankenyDiagMap n q ⁻¹' Metric.ball (0 : E3) (ankenyBallRadius n q)
end GeometryOfNumbers.Minkowski


import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Number theory utilities (local to this repo)

This module collects small “glue lemmas” that show up repeatedly in the Ankeny/Minkowski pipeline:

- converting simple modular facts (e.g. `n % 8 = 3`) into `Odd n`,
- turning `Odd n` into unit/coprime facts in `ZMod n`.

These are intentionally low-level and compositional: they are API building blocks, not theorems.
-/

namespace GeometryOfNumbers.NumberTheory

/-! ## Parity helpers -/

