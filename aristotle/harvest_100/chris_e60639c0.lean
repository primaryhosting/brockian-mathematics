/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: the required header comment must be the very first thing in the file, and
Lean does not allow `import` commands after a module docstring.  The development
below therefore uses only Lean 4 core (it needs nothing from Mathlib).
-/

universe u v w x

namespace Frontier

/--
**Good Regulator Theorem (Conant–Ashby), deterministic base case.**

Setting:
* `D` is the set of disturbances acting on the system;
* `S` is the state space of the system, i.e. the abstraction `σ : D → S` of a
  disturbance that actually matters for the system's behaviour;
* `R` is the set of regulatory actions;
* `Z` is the set of outcomes, produced by the system map `φ : D → R → Z`.

Hypotheses:
* `hsys` : the system is a genuine function of its state — the outcome map
  depends on the disturbance only through `σ`;
* `hinj` : for each disturbance, distinct regulatory actions produce distinct
  outcomes (the regulator has no redundant, mutually equivalent moves);
* `hgood` : the regulator `ρ` is *good* — it steers the outcome to the single
  goal value `z₀` whatever the disturbance.

Conclusion: the regulator **is (contains) a model of the system**: its action
factors through the state of the system, `ρ = m ∘ σ`, so reading off the
regulator's behaviour yields a map `m : S → R` defined on the system's own
state space.
-/
theorem good_regulator
    {D : Type u} {S : Type v} {R : Type w} {Z : Type x} [inst : Nonempty R]
    (σ : D → S) (φ : D → R → Z) (ρ : D → R) (z₀ : Z)
    (hsys : ∀ d d' : D, σ d = σ d' → φ d = φ d')
    (hinj : ∀ d : D, Function.Injective (φ d))
    (hgood : ∀ d : D, φ d (ρ d) = z₀) :
    ∃ m : S → R, ρ = m ∘ σ := by
  classical
  refine ⟨fun s => if h : ∃ d : D, σ d = s then ρ h.choose else Classical.choice inst, ?_⟩
  funext d
  have hex : ∃ d' : D, σ d' = σ d := ⟨d, rfl⟩
  simp only [Function.comp_apply, dif_pos hex]
  have hφ : φ hex.choose = φ d := hsys _ _ hex.choose_spec
  refine hinj d ?_
  rw [← hφ, hgood, ← hgood d, hφ]

/--
Complement to the theorem above: under the same non-redundancy assumption on
regulatory actions, the good regulator is *unique* — any two regulators that
both achieve the goal outcome `z₀` coincide.  Hence the model extracted in
`Frontier.good_regulator` is the only one.
-/
theorem good_regulator_unique
    {D : Type u} {R : Type w} {Z : Type x}
    (φ : D → R → Z) (ρ₁ ρ₂ : D → R) (z₀ : Z)
    (hinj : ∀ d : D, Function.Injective (φ d))
    (h₁ : ∀ d : D, φ d (ρ₁ d) = z₀) (h₂ : ∀ d : D, φ d (ρ₂ d) = z₀) :
    ρ₁ = ρ₂ := by
  funext d
  exact hinj d ((h₁ d).trans (h₂ d).symm)

end Frontier

import Mathlib

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

