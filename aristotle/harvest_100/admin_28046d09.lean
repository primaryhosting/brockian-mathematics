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
def GoodRegulator {S : Type u} {R : Type v} {Z : Type w} (ψ : S → R → Z) (z₀ : Z) (ρ : S → R) : Prop :=
  ∀ s : S, ψ s (ρ s) = z₀

/-- A system `ψ` is *sensitive* when, for every disturbance, distinct regulatory responses
lead to distinct outcomes. -/
def Sensitive {S : Type u} {R : Type v} {Z : Type w} (ψ : S → R → Z) : Prop :=
  ∀ s : S, Function.Injective (ψ s)

/-- The *behaviour map* of a system: each disturbance `s` is sent to the outcome function
`ψ s : R → Z` that it induces. -/
def behaviour {S : Type u} {R : Type v} {Z : Type w} (ψ : S → R → Z) : S → (R → Z) := ψ

/-- The *model* of a system: the type of behaviours actually realised by some disturbance,
i.e. the range of the behaviour map.  A map defined on `SystemModel ψ` is a function of the
system's model alone. -/
def SystemModel {S : Type u} {R : Type v} {Z : Type w} (ψ : S → R → Z) : Type _ :=
  {f : R → Z // ∃ s : S, behaviour ψ s = f}

/-- Every disturbance determines a point of the system's model. -/
def toModel {S : Type u} {R : Type v} {Z : Type w} (ψ : S → R → Z) (s : S) : SystemModel ψ :=
  ⟨behaviour ψ s, s, rfl⟩

/-!
## Auxiliary lemmas
-/

/-- For a sensitive system, a good regulator selects exactly the unique response that
achieves the target outcome. -/
theorem eq_of_good {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z} {z₀ : Z} (hsens : Sensitive ψ)
    {ρ : S → R} (hρ : GoodRegulator ψ z₀ ρ) (s : S) (r : R) :
    ψ s r = z₀ ↔ r = ρ s := by
  constructor
  · intro h
    exact hsens s (h.trans (hρ s).symm)
  · rintro rfl
    exact hρ s

/-- **Uniqueness of good regulators.**  For a sensitive system any two good regulators are
equal: the regulator is completely determined by the system. -/
theorem good_regulator_unique {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z} {z₀ : Z} (hsens : Sensitive ψ)
    {ρ ρ' : S → R} (hρ : GoodRegulator ψ z₀ ρ) (hρ' : GoodRegulator ψ z₀ ρ') :
    ρ' = ρ := by
  funext s
  exact (eq_of_good hsens hρ s (ρ' s)).1 (hρ' s)

/-- **The regulator depends only on the behaviour of the system.**  Disturbances with the
same system behaviour receive the same regulatory response. -/
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
theorem regulator_factors_through_model {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z} {z₀ : Z}
    (hsens : Sensitive ψ) {ρ : S → R} (hρ : GoodRegulator ψ z₀ ρ) :
    ∃ h : SystemModel ψ → R, ∀ s : S, ρ s = h (toModel ψ s) := by
  refine ⟨fun f => ρ (Classical.choose f.2), fun s => ?_⟩
  have hspec : behaviour ψ (Classical.choose (toModel ψ s).2) = behaviour ψ s :=
    Classical.choose_spec (toModel ψ s).2
  exact (regulator_congr_behaviour hsens hρ hspec).symm

/-- **The regulator's state space contains a model of the system.**  Distinct responses
induce distinct outcome-profiles `fun s => ψ s r`, so the states used by the regulator are
in bijection with the corresponding system behaviours: the regulator's state space carries
an isomorphic copy of that part of the system. -/
theorem states_inject_into_behaviours {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z}
    (hsens : Sensitive ψ) (r₁ r₂ : R) (s : S)
    (h : (fun t : S => ψ t r₁) = (fun t : S => ψ t r₂)) : r₁ = r₂ :=
  hsens s (congrFun h s)

/-- **The regulator's internal distinctions are exactly the system's distinctions.**  Two
disturbances receive the same response precisely when the response chosen for the first one
also regulates the second one to the target outcome.  Thus the equivalence relation that the
regulator imposes on disturbances is determined by the system alone. -/
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
theorem good_regulator {S : Type u} {R : Type v} {Z : Type w} {ψ : S → R → Z} {z₀ : Z}
    (hsens : Sensitive ψ) {ρ : S → R} (hρ : GoodRegulator ψ z₀ ρ) :
    (∀ s : S, ∀ r : R, ψ s r = z₀ ↔ r = ρ s) ∧
    (∀ ρ' : S → R, GoodRegulator ψ z₀ ρ' → ρ' = ρ) ∧
    (∃ h : SystemModel ψ → R, ∀ s : S, ρ s = h (toModel ψ s)) ∧
    (∀ s₁ s₂ : S, ρ s₁ = ρ s₂ ↔ ψ s₂ (ρ s₁) = z₀) ∧
    (∀ s₁ s₂ : S, (fun t : S => ψ t (ρ s₁)) = (fun t : S => ψ t (ρ s₂)) → ρ s₁ = ρ s₂) :=
  ⟨fun s r => eq_of_good hsens hρ s r,
   fun _ hρ' => good_regulator_unique hsens hρ hρ',
   regulator_factors_through_model hsens hρ,
   fun s₁ s₂ => regulator_kernel_iff hsens hρ s₁ s₂,
   fun s₁ s₂ h => states_inject_into_behaviours hsens (ρ s₁) (ρ s₂) s₁ h⟩

/-!
## Non-vacuity

The hypotheses are satisfiable: a two-state system in which the regulator must reproduce the
disturbance exactly.
-/

example : Sensitive (fun s r : Bool => decide (s = r)) := by
  unfold Sensitive Function.Injective
  decide

example : GoodRegulator (fun s r : Bool => decide (s = r)) true (fun s => s) := by
  intro s
  cases s <;> rfl

end Frontier

