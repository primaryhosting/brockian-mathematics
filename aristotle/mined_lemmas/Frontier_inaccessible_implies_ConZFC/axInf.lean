import Mathlib

/-!
# The cumulative hierarchy and inaccessible cardinals

This file defines the von Neumann cumulative hierarchy `Frontier.cumul o` inside `ZFSet`,
characterizes its members by rank, and proves the two facts about an inaccessible cardinal `κ`
that are needed to see that `V_κ` is a model of ZFC:

* `Frontier.card_lt_of_rank_lt`: a set of rank `< κ.ord` has cardinality `< κ`;
* `Frontier.rank_range_lt`: `V_κ` is closed under images of small families (replacement).
-/

open Ordinal Cardinal

namespace Frontier

/-- The von Neumann cumulative hierarchy `V_o`, as a `ZFSet`. -/

noncomputable def axInf : setLang.Sentence :=
  exQ ((exQ ((memF vz (up vz)) ⊓ (allQ (Formula.not (memF vz (up vz)))))) ⊓
    (allQ ((memF vz (up vz)).imp (exQ ((memF vz (up (up vz))) ⊓
      (allQ ((memF vz (up vz)).iff
        ((memF vz (up (up vz))) ⊔ (Term.equal vz (up (up vz)))))))))))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
