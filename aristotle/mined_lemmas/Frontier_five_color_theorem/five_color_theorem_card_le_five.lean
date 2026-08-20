import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

theorem five_color_theorem_card_le_five {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hV : Fintype.card V ≤ 5) : G.Colorable 5 :=
  five_color_theorem_of_reducible G
    (fiveColorReducible_of_card_le_five Finset.univ G (by simpa using hV))

/-- `G` is `4`-degenerate on `s`: every nonempty subset of `s` contains a vertex having at
most four neighbours inside that subset. -/
