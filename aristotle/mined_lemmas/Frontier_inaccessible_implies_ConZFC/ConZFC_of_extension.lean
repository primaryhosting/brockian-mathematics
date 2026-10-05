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

theorem ConZFC_of_extension {T : setLang.Theory} (hT : ZFC ⊆ T) (h : T.IsSatisfiable) :
    ZFC.IsSatisfiable :=
  h.mono hT

end Frontier

import Mathlib

/-!
# The first-order language of set theory and the axioms of ZFC

This file sets up the first-order language `Frontier.setLang` with a single binary relation
symbol `∈`, convenient combinators for building formulas (`allQ`, `exQ`, `memF`, `up`), and
the theory `Frontier.ZFC` consisting of

* extensionality, pairing, union, power set, infinity, foundation, choice, and
* the separation and replacement schemes (one instance for every formula with parameters).

For each axiom we prove a `Realize` lemma expressing satisfaction in an arbitrary structure in
readable mathematical terms.
-/

open FirstOrder Language

namespace Frontier

/-- The type of relation symbols of the language of set theory: one binary symbol. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: one binary relation symbol. -/
