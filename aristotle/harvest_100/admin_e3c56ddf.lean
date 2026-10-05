/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {D : Type u} {R : Type v} {Z : Type w}

/-
A **system** is described by a response map `psi : D → R → Z`: when the disturbance
(system state) is `d` and the regulator emits the action `a`, the outcome is `psi d a`.
-/

/-- `r` is a *good regulator* for the system `psi` with respect to the target outcome `z₀`
if it always steers the outcome to `z₀`, i.e. regulation succeeds for every disturbance. -/
def IsGoodRegulator (psi : D → R → Z) (z₀ : Z) (r : D → R) : Prop :=
  ∀ d, psi d (r d) = z₀

/-- `r` *is a model of the system* `psi`: the action chosen by the regulator depends on the
disturbance only through the system's own response behaviour `psi d : R → Z`. Equivalently,
the regulator's mapping factors through the system (see `good_regulator`). -/
def IsModel (psi : D → R → Z) (r : D → R) : Prop :=
  ∀ d d', psi d = psi d' → r d = r d'

/-- The system leaves the regulator *no unnecessary variety*: for each disturbance there is at
most one action achieving the target outcome. This is the deterministic base case of the
Conant–Ashby setting, in which an optimal regulator has no spare freedom in its choice of
action. -/
def NoSpareVariety (psi : D → R → Z) (z₀ : Z) : Prop :=
  ∀ d a b, psi d a = z₀ → psi d b = z₀ → a = b

/-- Contrapositive form of the base case: if the regulator makes a distinction that the system
itself does not make (`psi d = psi d'` but `r d ≠ r d'`), then either the regulator fails to
regulate, or the system does leave it spare variety. -/
theorem not_isModel_imp (psi : D → R → Z) (z₀ : Z) (r : D → R)
    (h : ¬ IsModel psi r) :
    ¬ IsGoodRegulator psi z₀ r ∨ ¬ NoSpareVariety psi z₀ := by
  by_cases hgood : IsGoodRegulator psi z₀ r
  · by_cases huniq : NoSpareVariety psi z₀
    · refine absurd (fun d d' hdd' => ?_) h
      have h1 : psi d' (r d) = z₀ := by rw [← hdd']; exact hgood d
      exact huniq d' (r d) (r d') h1 (hgood d')
    · exact Or.inr huniq
  · exact Or.inl hgood

/-- **Conant–Ashby good regulator theorem (deterministic base case).**
Every good regulator of a system is (contains) a model of that system: if `r` regulates the
system `psi` to the target outcome `z₀`, and the system leaves the regulator no spare variety,
then `r` is a model of `psi` — its behaviour is a function `m` of the system's own response
map, i.e. `r d = m (psi d)` for all disturbances `d`. (The `Nonempty R` instance is only needed
in order to name such an `m` when there are no disturbances at all; the factorisation of the
regulator through the system is the content of the statement.) -/
theorem good_regulator [Nonempty R] (psi : D → R → Z) (z₀ : Z) (r : D → R)
    (hgood : IsGoodRegulator psi z₀ r) (huniq : NoSpareVariety psi z₀) :
    IsModel psi r ∧ ∃ m : (R → Z) → R, ∀ d, r d = m (psi d) := by
  have hmodel : IsModel psi r := by
    by_cases h : IsModel psi r
    · exact h
    · cases not_isModel_imp psi z₀ r h with
      | inl h' => exact absurd hgood h'
      | inr h' => exact absurd huniq h'
  refine ⟨hmodel, ?_⟩
  letI : DecidablePred (fun f : R → Z => ∃ d, psi d = f) := fun _ => Classical.propDecidable _
  refine ⟨fun f => if h : ∃ d, psi d = f then r h.choose else Classical.choice inferInstance, ?_⟩
  intro d
  have hex : ∃ d', psi d' = psi d := ⟨d, rfl⟩
  show r d = if h : ∃ d', psi d' = psi d then r h.choose else Classical.choice inferInstance
  rw [dif_pos hex]
  exact hmodel d hex.choose hex.choose_spec.symm

/-- The hypotheses of `good_regulator` are satisfiable: the regulator that mirrors a binary
disturbance regulates the outcome to `true`, and it is the only action that does so. -/
example :
    IsGoodRegulator (fun d a : Bool => a == d) true (fun d => d) ∧
      NoSpareVariety (fun d a : Bool => a == d) true := by
  constructor
  · intro d; cases d <;> rfl
  · intro d a b ha hb; cases d <;> cases a <;> cases b <;> simp_all

end Frontier

#print axioms Frontier.good_regulator

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

