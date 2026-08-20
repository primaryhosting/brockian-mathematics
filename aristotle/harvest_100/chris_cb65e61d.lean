/-
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA
namespace Isolation

/-! ## The isolation model

A *capability* is an abstract resource token held by a sandboxed component.
A *policy* describes the delegation edges of the isolation engine: `pol.grant c d`
means that a component already holding capability `c` may acquire capability `d`.

The privilege set of a component is the set of capabilities it starts with; the
component *escapes* to a capability `t` if it can acquire `t` through some finite
chain of grants. -/

/-- Capabilities are identified by natural numbers. -/
abbrev Cap : Type := ℕ

/-- An isolation policy: the delegation edges available to the sandboxed component. -/
structure Policy where
  /-- `grant c d` : holding capability `c` permits acquiring capability `d`. -/
  grant : Cap → Cap → Prop

/-- `Reach pol P` is the set of capabilities obtainable from the initial privilege
set `P` by finitely many delegation steps of the policy `pol`. -/
inductive Reach (pol : Policy) (P : Set Cap) : Cap → Prop
  | base {c : Cap} : c ∈ P → Reach pol P c
  | step {c d : Cap} : Reach pol P c → pol.grant c d → Reach pol P d

/-- A component with privilege set `P` *escapes* to the capability `t` when `t` is
reachable from `P` under the policy. -/
def Escapes (pol : Policy) (P : Set Cap) (t : Cap) : Prop := Reach pol P t

/-! ## The isolation engine

The engine computes the reachable set by saturating the privilege set one
delegation layer at a time. -/

/-- One saturation layer of the engine: add every capability granted by something
already present. -/
def stepSet (pol : Policy) (S : Set Cap) : Set Cap :=
  S ∪ {d : Cap | ∃ c ∈ S, pol.grant c d}

/-- `engine pol P n` is the privilege set after `n` saturation rounds. -/
def engine (pol : Policy) (P : Set Cap) : ℕ → Set Cap
  | 0 => P
  | n + 1 => stepSet pol (engine pol P n)

/-! ## Basic structural lemmas -/

theorem subset_stepSet (pol : Policy) (S : Set Cap) : S ⊆ stepSet pol S := by
  intro x hx
  exact Or.inl hx

theorem stepSet_mono (pol : Policy) {S T : Set Cap} (h : S ⊆ T) :
    stepSet pol S ⊆ stepSet pol T := by
  rintro x (hx | ⟨c, hc, hcd⟩)
  · exact Or.inl (h hx)
  · exact Or.inr ⟨c, h hc, hcd⟩

theorem engine_mono_round (pol : Policy) (P : Set Cap) (n : ℕ) :
    engine pol P n ⊆ engine pol P (n + 1) := by
  simpa [engine] using subset_stepSet pol (engine pol P n)

theorem engine_mono_le (pol : Policy) (P : Set Cap) {m n : ℕ} (h : m ≤ n) :
    engine pol P m ⊆ engine pol P n := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (engine_mono_round pol P k)
      · have : m = k + 1 := le_antisymm h hge
        subst this
        exact subset_rfl

theorem engine_mono_priv (pol : Policy) {P Q : Set Cap} (h : P ⊆ Q) (n : ℕ) :
    engine pol P n ⊆ engine pol Q n := by
  induction n with
  | zero => simpa [engine] using h
  | succ k ih => exact stepSet_mono pol ih

/-! ## Soundness and completeness of the engine -/

/-- **Soundness**: everything the engine reports as obtainable really is reachable. -/
theorem engine_sound (pol : Policy) (P : Set Cap) (n : ℕ) :
    engine pol P n ⊆ {t : Cap | Reach pol P t} := by
  induction n with
  | zero => intro x hx; exact Reach.base hx
  | succ k ih =>
      rintro x (hx | ⟨c, hc, hcd⟩)
      · exact ih hx
      · exact Reach.step (ih hc) hcd

/-- **Completeness**: every reachable capability is found by the engine after
finitely many rounds. -/
theorem engine_complete (pol : Policy) (P : Set Cap) {t : Cap} (h : Reach pol P t) :
    ∃ n : ℕ, t ∈ engine pol P n := by
  induction h with
  | base hc => exact ⟨0, hc⟩
  | step _ hcd ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr ⟨_, hn, hcd⟩⟩

/-- The engine's model is exactly the reachability semantics. -/
theorem engine_iff_reach (pol : Policy) (P : Set Cap) (t : Cap) :
    (∃ n : ℕ, t ∈ engine pol P n) ↔ Reach pol P t :=
  ⟨fun ⟨n, hn⟩ => engine_sound pol P n hn, engine_complete pol P⟩

/-! ## Monotonicity of privilege escape -/

/-- Reachability is monotone in the initial privilege set. -/
theorem reach_mono (pol : Policy) {P Q : Set Cap} (h : P ⊆ Q) {t : Cap}
    (ht : Reach pol P t) : Reach pol Q t := by
  induction ht with
  | base hc => exact Reach.base (h hc)
  | step _ hcd ih => exact Reach.step ih hcd

/-- **Privilege escape is monotone**: enlarging the privilege set of a sandboxed
component can only enlarge the set of capabilities it can escape to. In particular
an isolation proof for the larger privilege set implies one for the smaller. -/
theorem priv_escape_monotone (pol : Policy) {P Q : Set Cap} (h : P ⊆ Q) {t : Cap}
    (ht : Escapes pol P t) : Escapes pol Q t :=
  reach_mono pol h ht

/-- Contrapositive form: if the larger privilege set is isolated from `t`, so is the
smaller one. -/
theorem isolation_antitone (pol : Policy) {P Q : Set Cap} (h : P ⊆ Q) {t : Cap}
    (ht : ¬ Escapes pol Q t) : ¬ Escapes pol P t :=
  fun hP => ht (priv_escape_monotone pol h hP)

/-- The escape relation is nontrivial: a component holding `c` with a grant edge to
`t` really does escape to `t`, while the empty privilege set escapes nowhere. -/
theorem escapes_of_grant (pol : Policy) {P : Set Cap} {c t : Cap} (hc : c ∈ P)
    (hg : pol.grant c t) : Escapes pol P t :=
  Reach.step (Reach.base hc) hg

theorem not_escapes_empty (pol : Policy) (t : Cap) : ¬ Escapes pol (∅ : Set Cap) t := by
  intro h
  induction h with
  | base hc => exact hc
  | step _ _ ih => exact ih

end Isolation
end PCA

