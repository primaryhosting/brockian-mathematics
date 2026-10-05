/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalization of the base (deterministic, error-free) case of the Conant–Ashby
"Every good regulator of a system must be a model of that system" theorem.

Setting.  `D` is the type of disturbances acting on the system, `R` the type of
regulatory actions, and `Z` the type of outcomes.  The system is described by its
outcome map `Φ : D → R → Z`: under disturbance `d`, taking action `r` produces the
outcome `Φ d r`.  A regulator is a map `ρ : D → R`, and it is *good* (successful)
when it always attains the target outcome `goal`, i.e. `Φ d (ρ d) = goal` for all `d`.

Hypothesis.  For each disturbance the system is *discriminating*: distinct actions
produce distinct outcomes, `Function.Injective (Φ d)`.  (This is the deterministic
counterpart of Conant–Ashby's requirement that the optimal regulator be
entropy-minimizing / that the regulation be error-free.)

Conclusion.  A good regulator *is a model of the system*: its action is computed
from the system's behaviour `Φ d` alone, by the universal "model" map `modelMap`,
which does not depend on the regulator.  Consequently the good regulator is unique,
and it factors through the system's behaviour (disturbances with the same behaviour
receive the same regulatory action) — the regulator is an isomorphic image of the
system, which is Conant–Ashby's conclusion.

The file is self-contained (Lean core only); no Mathlib lemma closes it directly,
the only library ingredients used are `Exists.choose`/`Exists.choose_spec`,
`dif_pos` and `Function.Injective`.
-/

universe u v w

namespace Frontier

open Classical in
/-- The *model* of the system: from a system behaviour `f : R → Z` (the outcome of
each regulatory action under some fixed disturbance) it reads off the action that
attains the target outcome `goal`. -/

noncomputable def modelMap {R : Type v} {Z : Type w} [Nonempty R] (goal : Z) (f : R → Z) : R :=
  if h : ∃ r, f r = goal then h.choose else Classical.ofNonempty

/--
**Good regulator theorem** (Conant–Ashby, deterministic base case).

Let `Φ : D → R → Z` be a system mapping a disturbance `d` and a regulatory action `r`
to an outcome, such that for each disturbance distinct actions give distinct outcomes.
If a regulator `ρ : D → R` is *good*, i.e. it always attains the target outcome `goal`,
then:

1. `ρ` is (contains) a model of the system: `ρ d = modelMap goal (Φ d)`, so the
   regulator's output is obtained from the system's behaviour by a fixed map that is
   independent of `ρ`;
2. `ρ` is the unique good regulator;
3. `ρ` factors through the system's behaviour: equal behaviours force equal actions.
-/
