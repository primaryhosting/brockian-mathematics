import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem encodeCNFP_eval (k : ℕ) (F : PCnf) (x : List Bool)
    (hcon : ∀ c ∈ F, PClause.Consistent c) :
    (encodeCNFP k F).map (fun p => p.eval x) = encodeCNF k (PCnf.inst x F) := by
  simp only [encodeCNFP, encodeCNF, List.map_map]
  refine List.map_congr_left ?_
  intro t _
  simp only [Function.comp_apply, encodeBitP, encodeBit]
  exact encodeBitP_aux x F _ _ _ hcon

end Frontier

import Mathlib
import RequestProject.CookLevin

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import RequestProject.Circuit

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Tseitin transformation

Given a circuit `gs`, we build a CNF formula whose satisfying assignments are exactly the
accepting computations of the circuit.  Some of the circuit's input variables may be
*fixed* to prescribed truth values; the remaining ones stay free.

We use `Std.Sat.CNF ℕ` as the type of CNF formulas: a clause is a list of literals
`(v, b)`, satisfied by the assignment `a` when `a v = b`.

Variables of the produced formula: `gv j = 2 * j` stands for the value of gate `j`,
and `iv i = 2 * i + 1` stands for the value of the (free) input variable `i`.
-/

namespace Frontier

open Std.Sat

/-- A bit that either is a constant or reads (the negation of) one bit of the input word.
These are used to describe *projection* reductions. -/
inductive ProjBit where
  | cst (b : Bool)
  | pos (i : ℕ)
  | neg (i : ℕ)
  deriving DecidableEq, Repr

/-- Value of a projection bit on the input word `x`. -/
