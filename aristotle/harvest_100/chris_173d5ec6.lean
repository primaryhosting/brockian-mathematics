/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/--
**Conant–Ashby "Good Regulator" theorem (deterministic base case).**

Setting: a system with state space `S`, a regulator with action space `R`, and an
outcome map `h : S → R → Z`.  The regulation goal is the single "good" outcome `z₀`
(the error-free, minimal-entropy case of the Conant–Ashby setup).

Hypothesis `hgood`: for every system state there is exactly one regulator action that
achieves the good outcome — i.e. regulation is possible and of minimal variety.

Conclusion: there is a map `m : S → R` such that

* `m` is a successful regulator;
* **every** good regulator equals `m`, so a good regulator is necessarily a *function of
  the system state*: it is a model of the system;
* `m s = m s'` holds exactly when `s` and `s'` impose the same requirement on the
  regulator.  Hence the regulator's actions are in bijection with the distinguishable
  states of the system: the regulator *contains a model* of the system.

The proof is elementary; the whole content is the uniqueness clause packaged in
`hgood` (this is exactly Mathlib's `ExistsUnique.unique`, spelled out here), so the file
needs no imports at all.
-/
theorem good_regulator {S R Z : Type _} (h : S → R → Z) (z₀ : Z)
    (hgood : ∀ s, ∃ r, h s r = z₀ ∧ ∀ r', h s r' = z₀ → r' = r) :
    ∃ m : S → R,
      (∀ s, h s (m s) = z₀) ∧
      (∀ ρ : S → R, (∀ s, h s (ρ s) = z₀) → ρ = m) ∧
      (∀ s s', m s = m s' ↔ ∀ r, (h s r = z₀ ↔ h s' r = z₀)) := by
  classical
  refine ⟨fun s => Classical.choose (hgood s), fun s => (Classical.choose_spec (hgood s)).1,
    ?_, ?_⟩
  · intro ρ hρ
    funext s
    exact (Classical.choose_spec (hgood s)).2 (ρ s) (hρ s)
  · intro s s'
    have hs := Classical.choose_spec (hgood s)
    have hs' := Classical.choose_spec (hgood s')
    show Classical.choose (hgood s) = Classical.choose (hgood s') ↔ _
    constructor
    · intro hss' r
      constructor
      · intro hr
        have hrs : r = Classical.choose (hgood s) := hs.2 r hr
        rw [hrs, hss']
        exact hs'.1
      · intro hr
        have hrs : r = Classical.choose (hgood s') := hs'.2 r hr
        rw [hrs, ← hss']
        exact hs.1
    · intro hiff
      exact hs'.2 _ ((hiff _).mp hs.1)

end Frontier

/-
# Good Regulator — Mathlib development

Companion file to `RequestProject/GoodRegulator.lean`, which contains the target
theorem `Frontier.good_regulator`.  (That file must open with a fixed header comment,
so it cannot carry an `import` line; the Mathlib-based development lives here.)

Here the Conant–Ashby statement is developed with Mathlib's `ExistsUnique`, and the
"contains a model" clause is upgraded to an explicit equivalence between the
distinguishable states of the system and the actions actually used by the regulator.
-/

import Mathlib

namespace Frontier

variable {S R Z : Type*}

/-- Two system states are *indistinguishable* (for the regulation goal `z₀`) when they
demand the same thing of the regulator: exactly the same actions succeed on both. -/
def sysSetoid (h : S → R → Z) (z₀ : Z) : Setoid S where
  r s s' := ∀ r, h s r = z₀ ↔ h s' r = z₀
  iseqv :=
    { refl := fun _ _ => Iff.rfl
      symm := fun hss' r => (hss' r).symm
      trans := fun h₁ h₂ r => (h₁ r).trans (h₂ r) }

section Model

variable (h : S → R → Z) (z₀ : Z) (hgood : ∀ s, ∃! r, h s r = z₀)

/-- The model of the system extracted from a perfectly regulable setup: `regulatorModel`
sends a system state to the unique regulator action that achieves the good outcome. -/
noncomputable def regulatorModel : S → R := fun s => (hgood s).exists.choose

variable {h z₀}

theorem regulatorModel_spec (s : S) : h s (regulatorModel h z₀ hgood s) = z₀ :=
  (hgood s).exists.choose_spec

theorem eq_regulatorModel {s : S} {r : R} (hr : h s r = z₀) :
    r = regulatorModel h z₀ hgood s :=
  (hgood s).unique hr (regulatorModel_spec hgood s)

include hgood in
/-- **Good regulator theorem, `ExistsUnique` form.**  There is exactly one good
regulator, and it is a function of the system state — a model of the system. -/
theorem good_regulator_existsUnique : ∃! ρ : S → R, ∀ s, h s (ρ s) = z₀ := by
  refine ⟨regulatorModel h z₀ hgood, regulatorModel_spec hgood, ?_⟩
  intro ρ hρ
  funext s
  exact eq_regulatorModel hgood (hρ s)

/-- The model map identifies precisely the indistinguishable system states. -/
theorem regulatorModel_eq_iff (s s' : S) :
    regulatorModel h z₀ hgood s = regulatorModel h z₀ hgood s' ↔
      (sysSetoid h z₀).r s s' := by
  constructor
  · intro hss' r
    constructor
    · intro hr
      have : r = regulatorModel h z₀ hgood s := eq_regulatorModel hgood hr
      rw [this, hss']
      exact regulatorModel_spec hgood s'
    · intro hr
      have : r = regulatorModel h z₀ hgood s' := eq_regulatorModel hgood hr
      rw [this, ← hss']
      exact regulatorModel_spec hgood s
  · intro hiff
    exact eq_regulatorModel hgood ((hiff _).mp (regulatorModel_spec hgood s))

theorem sysSetoid_eq_ker : sysSetoid h z₀ = Setoid.ker (regulatorModel h z₀ hgood) :=
  Setoid.ext fun s s' => (regulatorModel_eq_iff hgood s s').symm

/-- **The regulator contains a model of the system.**  The distinguishable states of the
system correspond bijectively to the regulator actions actually used: the regulator's
own state space is (an isomorphic copy of) the system's. -/
noncomputable def modelEquiv :
    Quotient (sysSetoid h z₀) ≃ Set.range (regulatorModel h z₀ hgood) :=
  (Quotient.congr (Equiv.refl S) fun s s' => by
      simpa [Setoid.ker, Function.onFun] using (regulatorModel_eq_iff hgood s s').symm).trans
    (Setoid.quotientKerEquivRange _)

@[simp]
theorem modelEquiv_apply (s : S) :
    (modelEquiv hgood (Quotient.mk (sysSetoid h z₀) s) : R) = regulatorModel h z₀ hgood s :=
  rfl

end Model

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

