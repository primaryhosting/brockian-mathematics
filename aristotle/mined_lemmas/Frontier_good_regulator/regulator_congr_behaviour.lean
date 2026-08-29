/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The requested header comment must be the very first thing in this file, and Lean 4 does not
allow an `import` command to be preceded by a module doc comment.  The development below is
therefore written so that it needs no imports at all: it uses only Lean core notions
(`Function.Injective`, `Classical.choose`, subtypes).  The original preamble of this file is
retained below, except for the `open scoped ...` lines, which require `import Mathlib` and are
kept here in commented form:

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
-/

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

universe u v w

namespace Frontier

/-!
## Setting

We formalise the deterministic base case of the Conant–Ashby *Good Regulator* theorem
("Every good regulator of a system must be a model of that system", 1970).

* `S` is the type of **disturbances** (states of the regulated system),
* `R` is the type of **regulatory responses**,
* `Z` is the type of **outcomes**,
* `ψ : S → R → Z` is the **system**: it maps a disturbance together with a response to an
  outcome.  For a fixed disturbance `s`, the function `ψ s : R → Z` is the *behaviour* of
  the system under that disturbance.
* A **regulator** is a map `ρ : S → R`; it is **good** (it regulates perfectly with respect
  to the target outcome `z₀`) when it steers every disturbance to `z₀`.

The system is assumed **sensitive**: for each disturbance, distinct responses produce
distinct outcomes (`ψ s` is injective).  This is the standard non-degeneracy hypothesis:
without it a regulator could discard information about the disturbance simply because
several responses happen to be interchangeable.
-/

/-- A regulator `ρ` is *good* for the system `ψ` with target outcome `z₀` when every
disturbance is regulated to the outcome `z₀`. -/

theorem regulator_congr_behaviour {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z} {z₀ : Z}
    (hsens : Sensitive ψ) {ρ : S → R} (hρ : GoodRegulator ψ z₀ ρ) {s₁ s₂ : S}
    (h : behaviour ψ s₁ = behaviour ψ s₂) : ρ s₁ = ρ s₂ := by
  have h₂ : ψ s₁ (ρ s₂) = z₀ := by
    have hb : ψ s₁ = ψ s₂ := h
    rw [hb]
    exact hρ s₂
  exact ((eq_of_good hsens hρ s₁ (ρ s₂)).1 h₂).symm

/-- **A good regulator is a model of the system.**  There is a map `h` defined on the
system's model `SystemModel ψ` — that is, a function of the system alone — such that the
regulator is the composite of `h` with the behaviour map.  So the regulator's input-output
mapping *is* a mapping of the model of the system. -/
