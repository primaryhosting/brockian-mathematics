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


def inP (O : Oracle) (L : Set Str) : Prop :=
  ∃ (p : Prog) (k : ℕ), (∀ x : Str, cost O p x [] ≤ (x.length + 2) ^ k) ∧
    (∀ x : Str, x ∈ L ↔ accepts O p x [])

/-- `L ∈ NP^O`: there is a verifier running in time `(|x|+2)^k` on all witnesses of
length at most `(|x|+2)^k`, accepting some such witness exactly for `x ∈ L`. -/
