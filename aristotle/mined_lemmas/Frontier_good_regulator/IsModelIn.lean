/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v w

namespace Frontier

attribute [local instance] Classical.propDecidable

/-!
## Setting

We formalise the deterministic base case of the Conant–Ashby "good regulator" theorem.

* `S` is the set of states of the *system* (the disturbances acting on it),
* `R` is the set of *regulatory actions*,
* `Z` is the set of *outcomes*,
* `ψ : S → R → Z` is the system's outcome map: `ψ s r` is the outcome when the system is in
  state `s` and the regulator acts by `r`.

The *behaviour* of the system in state `s` is the whole function `ψ s : R → Z`; two states with
the same behaviour are indistinguishable from the outside. Thus `ψ : S → (R → Z)` presents the
system through its input/output behaviour, and a *model of the system contained in the regulator*
is a map `m : (R → Z) → R` reproducing the regulator's actions from that behaviour, i.e.
`ρ = m ∘ ψ`.
-/

/-- A regulator `ρ` is *good* (perfectly regulating) for the system `ψ` with target outcome `z₀`
if it forces the outcome `z₀` whatever the state of the system. -/

def IsModelIn {S : Type u} {R : Type v} {Z : Type w}
    (psi : S → R → Z) (rho : S → R) (m : (R → Z) → R) : Prop :=
  ∀ s : S, m (psi s) = rho s

/-- A good regulator of a tight system depends on the state of the system only through the
system's behaviour: indistinguishable states receive identical regulatory actions. -/
