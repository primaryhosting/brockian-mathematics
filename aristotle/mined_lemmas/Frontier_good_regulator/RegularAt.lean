/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-!
## Setting

We formalise the deterministic (base) case of the Conant–Ashby "Good Regulator"
theorem: *every good regulator of a system is (contains) a model of that system*.

The set‑up is Conant and Ashby's:

* `S` is the set of disturbances / states of the regulated system,
* `R` is the set of actions available to the regulator,
* `Z` is the set of outcomes,
* `sys : S → R → Z` is the system: it maps a disturbance and a regulatory action
  to an outcome,
* `goal : Z` is the single acceptable ("good") outcome.

A regulator is a map `ρ : S → R` (it observes the disturbance and picks an
action). It is *good* when the outcome is always acceptable, i.e. the outcome
variable is constant — the deterministic form of "the entropy of the outcome is
minimal".

The system is *regular* at `goal` when for each disturbance exactly one action
achieves the goal; this is Conant and Ashby's standing assumption that the
optimal response is well defined.

The conclusion is that a good regulator *is* a model of the system: its mapping
is uniquely determined by the system, `ρ s` being exactly the system's optimal
response to `s`; equivalently, from `ρ` alone one can read off, for every
disturbance and action, whether that action is the successful one. Any two good
regulators therefore coincide.

No Mathlib result states this theorem; the argument is elementary and the only
library lemma it needs is function extensionality (`funext`), used to pass from
pointwise agreement of two good regulators to equality of the two mappings.
The file therefore has no imports and is axiom-clean.

Finally, "contains a model": a regulator whose action is computed through an
internal representation, `ρ = act ∘ rep`, must have an internal representation
`rep` which already distinguishes disturbances at least as finely as the model
does, and through which the model factors.
-/

section

universe u v w x

variable {S : Type u} {R : Type v} {Z : Type w}

/-- A regulator `ρ` is **good** for the system `sys` with target outcome `goal`
when every disturbance is met with an action producing the target outcome. -/

def RegularAt (sys : S → R → Z) (goal : Z) : Prop :=
  ∀ s, ∃ r, sys s r = goal ∧ ∀ r', sys s r' = goal → r' = r

/-- A map `m : S → R` is a **model** of the system `sys` (relative to `goal`)
when it captures the whole success relation of the system: an action succeeds
against a disturbance exactly when it is the one prescribed by `m`. -/
