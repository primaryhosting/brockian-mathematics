import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian


def wheelSearch727 : Bool :=
  (List.range 728).all fun n =>
    !(decide (4 ≤ n) && (n % 2 == 0)) ||
      wheelPrimes727.any fun p => wheelPrimes727.contains (n - p)

set_option maxRecDepth 100000 in
