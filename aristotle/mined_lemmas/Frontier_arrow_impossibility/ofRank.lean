import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


def ofRank (r : α → Nat) (hr : ∀ x y, r x = r y → x = y) : Ranking α where
  lt := fun x y => r x < r y
  tr := fun h1 h2 => Nat.lt_trans h1 h2
  tot := fun x y hxy => by
    have h : r x ≠ r y := fun he => hxy (hr x y he)
    omega
  asym := fun h => Nat.lt_asymm h

