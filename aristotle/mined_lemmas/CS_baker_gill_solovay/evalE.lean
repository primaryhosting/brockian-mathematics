/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGSModel

/-!
## Basic properties of the machine model

* costs and query lists only grow;
* the cost of a run does not depend on the cost already accumulated (`run_shift`);
* every recorded query has length at most the cost, and there are at most `cost`
  many queries (`run_QInv`);
* locality: a run only depends on the oracle at the strings it queries
  (`run_local`).
-/

namespace CS.BGS

variable {O O' : Oracle} {st : State} {i : ℕ} {s : Str} {a b c e : Expr}

/-! ### Unfolding lemmas -/


def evalE (O : Oracle) : Expr → State → Str × State
  | .var i, st => (st.vars i, { st with cost := st.cost + 1 })
  | .lit s, st => (s, { st with cost := st.cost + s.length + 1 })
  | .cat a b, st =>
      let ra := evalE O a st
      let rb := evalE O b ra.2
      (ra.1 ++ rb.1, { rb.2 with cost := rb.2.cost + ra.1.length + rb.1.length + 1 })
  | .smash a b, st =>
      let ra := evalE O a st
      let rb := evalE O b ra.2
      (List.replicate (ra.1.length * rb.1.length) false,
        { rb.2 with cost := rb.2.cost + ra.1.length * rb.1.length + 1 })
  | .tail a, st =>
      let ra := evalE O a st
      (ra.1.tail, { ra.2 with cost := ra.2.cost + 1 })
  | .eqE a b, st =>
      let ra := evalE O a st
      let rb := evalE O b ra.2
      ((if ra.1 = rb.1 then [true] else []),
        { rb.2 with cost := rb.2.cost + ra.1.length + rb.1.length + 1 })
  | .query a, st =>
      let ra := evalE O a st
      ((if O ra.1 then [true] else []),
        { ra.2 with cost := ra.2.cost + ra.1.length + 1, qs := ra.1 :: ra.2.qs })

/-- Execution of programs. -/
