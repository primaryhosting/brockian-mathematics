import Mathlib
import RequestProject.Main

/-!
# Hardy Paradox — measure-theoretic form and a quantum-style witness

Companion to `RequestProject/Main.lean`, which contains the target theorem
`QI.hardy_paradox`.  Here we record

* `QI.hardy_paradox_measure`: the same impossibility for an arbitrary local hidden
  variable model given by a measure on the hidden variable space, and
* `QI.hardyBox`: an explicit no-signaling behaviour satisfying all four Hardy
  conditions with Hardy fraction `1/2`, showing that the hypotheses of the paradox
  are jointly realisable by a nonlocal (but no-signaling) theory, so that the
  statement is not vacuous.
-/

open scoped BigOperators

namespace QI

open MeasureTheory

/-- The set-theoretic form of Hardy's argument: the Hardy event is contained in the union
of the three forbidden events. -/

lemma hardyBox_no_signaling_A (x y y' a : Bool) :
    ∑ b : Bool, hardyBox x y a b = ∑ b : Bool, hardyBox x y' a b := by
  cases x <;> cases y <;> cases y' <;> cases a <;> simp [hardyBox]

/-- No-signaling from Alice to Bob: Bob's marginal does not depend on Alice's setting. -/
