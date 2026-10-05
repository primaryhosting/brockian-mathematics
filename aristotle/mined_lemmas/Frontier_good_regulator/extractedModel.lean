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

noncomputable def extractedModel {S : Type u} {R : Type v} {Z : Type w}
    [hR : Nonempty R] (psi : S → R → Z) (rho : S → R) : (R → Z) → R :=
  fun f => if h : ∃ s : S, psi s = f then rho (Classical.choose h) else Classical.choice hR

/-- **Every good regulator of a system is (contains) a model of that system** (Conant–Ashby,
deterministic base case).

Given a system `psi : S → R → Z` in which the target outcome `z0` pins down the regulatory
action (`TightAt`), any perfectly regulating `rho` satisfies:

1. **(model)** there is a map `m : (R → Z) → R` from the system's behaviour to regulatory actions
   with `rho = m ∘ psi`; the regulator is thus a mapping of the system's behaviour, and this
   model is itself a good regulator, since acting by `m (psi s)` always yields the target
   outcome;
2. **(uniqueness)** `rho` is the *only* good regulator, so no good regulator can avoid containing
   this model. -/
