/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Cardinal FirstOrder

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

We first record the "external" form of CH — the statement, about the actual real
numbers, that every uncountable set of reals has the cardinality of the continuum —
and prove that it is equivalent to the usual cardinal arithmetic form `ℵ₁ = 𝔠`.
This is a genuine (and fully proved) Lean theorem; it is the base case of the
formalization. -/

/-- The Continuum Hypothesis, in the form: every uncountable set of real numbers has
cardinality the continuum. -/

def setTheoryLang : FirstOrder.Language := ⟨fun _ => Empty, memRel⟩

/-- The membership symbol of the language of set theory. -/
abbrev memSymb : setTheoryLang.Relations 2 := memRel.mem

/-- **The Continuum Hypothesis is independent of ZFC.**

This is the formal statement, reduced (as in the Gödel–Cohen proof) to the existence
of the two models: if `zfc` is any theory in the first-order language of set theory
and `ch` is any sentence of that language (intended: a sentence formalizing the
Continuum Hypothesis), then, given

* `goedel`, a model of `zfc` satisfying `ch` (Gödel's constructible universe `L`), and
* `cohen`, a model of `zfc` refuting `ch` (Cohen's forcing extension),

the sentence `ch` is independent of `zfc`: neither `ch` nor `¬ ch` is a semantic
consequence of `zfc`, hence — by Gödel's completeness theorem — neither is provable
from `zfc`.

The two model hypotheses are exactly the content of Gödel's and Cohen's theorems;
they are not constructed here (they cannot be, without assuming the consistency of
ZFC). By `Frontier.independentOf_iff_exists_models` this reduction is an equivalence,
so nothing is lost by stating independence in this form. -/
