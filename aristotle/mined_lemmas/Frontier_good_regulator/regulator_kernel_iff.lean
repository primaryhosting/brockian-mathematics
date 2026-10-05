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

theorem regulator_kernel_iff {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z} {z₀ : Z}
    (hsens : Sensitive ψ) {ρ : S → R} (hρ : GoodRegulator ψ z₀ ρ) (s₁ s₂ : S) :
    ρ s₁ = ρ s₂ ↔ ψ s₂ (ρ s₁) = z₀ :=
  (eq_of_good hsens hρ s₂ (ρ s₁)).symm

/-!
## The Good Regulator theorem
-/

/-- **Good Regulator Theorem (Conant–Ashby), deterministic base case.**

Let `ψ : S → R → Z` be a sensitive system (for each disturbance, distinct responses give
distinct outcomes) and let `ρ : S → R` be a good regulator, i.e. one that steers every
disturbance to the target outcome `z₀`.  Then:

1. `ρ` selects precisely the unique response that achieves the target outcome;
2. `ρ` is the *only* good regulator — it is completely determined by the system;
3. `ρ` factors through the behaviour map `s ↦ ψ s`, i.e. the regulator is a function of the
   model `SystemModel ψ` of the system alone;
4. the distinctions the regulator makes between disturbances are exactly distinctions of
   the system: `ρ s₁ = ρ s₂` iff the response chosen for `s₁` also regulates `s₂`;
5. distinct responses used by the regulator correspond to distinct system behaviours, so the
   states of the regulator are an isomorphic image — a model — of the relevant part of the
   system.

Together, (3)–(5) formalise the Conant–Ashby conclusion: every good regulator of a system
is (and contains) a model of that system. -/
