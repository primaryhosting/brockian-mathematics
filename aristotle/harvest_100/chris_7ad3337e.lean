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

/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

universe u v

/-- A configuration of the isolation engine: `c d p` says that domain `d` currently
holds privilege `p`. -/
abbrev Config (Dom : Type u) (Priv : Type v) : Type max u v := Dom → Priv → Prop

/-- The configuration obtained from `c` by granting privilege `p` to domain `d`. -/
def grantAt {Dom : Type u} {Priv : Type v} (c : Config Dom Priv) (d : Dom) (p : Priv) :
    Config Dom Priv :=
  fun x q => c x q ∨ (x = d ∧ q = p)

/-- An isolation policy: `grant c d p` says that, in configuration `c`, the engine
permits privilege `p` to be handed to domain `d`. -/
structure Policy (Dom : Type u) (Priv : Type v) : Type max u v where
  /-- The permitted single-step grants. -/
  grant : Config Dom Priv → Dom → Priv → Prop

/-- `P.Le Q` : policy `Q` is at least as permissive as policy `P`. -/
def Policy.Le {Dom : Type u} {Priv : Type v} (P Q : Policy Dom Priv) : Prop :=
  ∀ c d p, P.grant c d p → Q.grant c d p

/-- Reachability of configurations under a policy: the reflexive-transitive closure
of the permitted single-step grants. -/
inductive Reach {Dom : Type u} {Priv : Type v} (P : Policy Dom Priv) :
    Config Dom Priv → Config Dom Priv → Prop
  | refl (c : Config Dom Priv) : Reach P c c
  | step {c c' : Config Dom Priv} {d : Dom} {p : Priv} :
      Reach P c c' → P.grant c' d p → Reach P c (grantAt c' d p)

/-- A privilege escape: starting from `c`, the engine can reach a configuration in
which domain `d` holds privilege `p`, even though it did not hold it initially. -/
def Escapes {Dom : Type u} {Priv : Type v} (P : Policy Dom Priv) (c : Config Dom Priv)
    (d : Dom) (p : Priv) : Prop :=
  ¬ c d p ∧ ∃ c', Reach P c c' ∧ c' d p

/-- A single permitted grant of a privilege the domain does not already hold is an
escape; in particular `Escapes` is not a vacuous notion. -/
theorem escapes_of_grant {Dom : Type u} {Priv : Type v} {P : Policy Dom Priv}
    {c : Config Dom Priv} {d : Dom} {p : Priv} (hnot : ¬ c d p) (hg : P.grant c d p) :
    Escapes P c d p :=
  ⟨hnot, grantAt c d p, Reach.step (Reach.refl c) hg, Or.inr ⟨rfl, rfl⟩⟩

/-- Reachability is monotone in the policy. -/
theorem reach_mono {Dom : Type u} {Priv : Type v} {P Q : Policy Dom Priv} (hPQ : P.Le Q)
    {c c' : Config Dom Priv} (h : Reach P c c') : Reach Q c c' := by
  induction h with
  | refl => exact Reach.refl _
  | step _ hg ih => exact Reach.step ih (hPQ _ _ _ hg)

/-- **Privilege escape is monotone in the policy.**  If policy `Q` permits every grant
that policy `P` permits, then every privilege escape possible under `P` is also
possible under `Q`. -/
theorem priv_escape_monotone {Dom : Type u} {Priv : Type v} {P Q : Policy Dom Priv}
    (hPQ : P.Le Q) {c : Config Dom Priv} {d : Dom} {p : Priv} (h : Escapes P c d p) :
    Escapes Q c d p := by
  obtain ⟨hnot, c', hreach, hmem⟩ := h
  exact ⟨hnot, c', reach_mono hPQ hreach, hmem⟩

/-- Contrapositive form: if the more permissive policy `Q` isolates `d` from `p`
(no escape is possible), then so does the more restrictive policy `P`. -/
theorem no_escape_antitone {Dom : Type u} {Priv : Type v} {P Q : Policy Dom Priv}
    (hPQ : P.Le Q) {c : Config Dom Priv} {d : Dom} {p : Priv} (h : ¬ Escapes Q c d p) :
    ¬ Escapes P c d p :=
  fun hP => h (priv_escape_monotone hPQ hP)

/-! ## A concrete instance: the implication is strict

The following witnesses show that the model is inhabited in a non-degenerate way:
privilege escapes really do occur under a permissive policy, and the converse of
`priv_escape_monotone` fails. -/

/-- The empty configuration on one domain and one privilege. -/
def emptyConfig : Config Unit Unit := fun _ _ => False

/-- The policy that permits nothing. -/
def denyAll : Policy Unit Unit := ⟨fun _ _ _ => False⟩

/-- The policy that permits every grant. -/
def allowAll : Policy Unit Unit := ⟨fun _ _ _ => True⟩

theorem denyAll_le_allowAll : denyAll.Le allowAll := fun _ _ _ _ => trivial

/-- Under `denyAll`, nothing new is ever reachable. -/
theorem reach_denyAll {c c' : Config Unit Unit} (h : Reach denyAll c c') :
    ∀ d p, c' d p → c d p := by
  induction h with
  | refl => exact fun _ _ h => h
  | step _ hg _ => exact absurd hg id

/-- `allowAll` admits a privilege escape from the empty configuration. -/
theorem allowAll_escapes : Escapes allowAll emptyConfig () () :=
  escapes_of_grant (fun h => h) trivial

/-- `denyAll` admits no privilege escape from the empty configuration. -/
theorem denyAll_not_escapes : ¬ Escapes denyAll emptyConfig () () := by
  rintro ⟨-, c', hreach, hmem⟩
  exact reach_denyAll hreach () () hmem

/-- The converse of `priv_escape_monotone` fails: an escape under the more permissive
policy need not be an escape under the more restrictive one. -/
theorem priv_escape_monotone_converse_false :
    ∃ (P Q : Policy Unit Unit) (c : Config Unit Unit) (d p : Unit),
      P.Le Q ∧ Escapes Q c d p ∧ ¬ Escapes P c d p :=
  ⟨denyAll, allowAll, emptyConfig, (), (),
    denyAll_le_allowAll, allowAll_escapes, denyAll_not_escapes⟩

end PCA.Isolation

