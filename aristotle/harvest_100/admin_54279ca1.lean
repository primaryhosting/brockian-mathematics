/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace PCA.Fix

/-! ## The isolation engine model

A *proof-carrying app* is described by a manifest consisting of

* a command line (`cmd`),
* a list of granted roles (`roles`),
* an isolation policy (`policy`).

The isolation engine only ever produces *canonical* manifests: empty command
arguments are dropped and the role list is canonicalised (deduplicated and put
into a fixed order of decreasing privilege).  Re-configuring an app by applying
a list of policy edits re-runs the engine's build pipeline, so a priori it could
also change the command line or the roles.  The target theorem states that on
well-formed (i.e. engine-produced) manifests this never happens: altering the
policy preserves roles and command exactly. -/

/-- The roles an app can be granted. -/
inductive Role
  | reader
  | writer
  | admin
  deriving DecidableEq, Repr

/-- All roles, in the engine's canonical order (decreasing privilege). -/
def allRoles : List Role := [Role.admin, Role.writer, Role.reader]

/-- An isolation policy. -/
structure Policy where
  allowNet : Bool
  allowFS : Bool
  memLimit : Nat
  denied : List String
  deriving DecidableEq, Repr

/-- A single policy edit. -/
inductive Edit
  | setNet (b : Bool)
  | setFS (b : Bool)
  | setMem (n : Nat)
  | deny (cap : String)
  | permit (cap : String)
  deriving Repr

/-- Effect of a single edit on a policy. -/
def applyEdit (p : Policy) : Edit → Policy
  | .setNet b => { p with allowNet := b }
  | .setFS b => { p with allowFS := b }
  | .setMem n => { p with memLimit := n }
  | .deny c => { p with denied := if c ∈ p.denied then p.denied else c :: p.denied }
  | .permit c => { p with denied := p.denied.filter (· ≠ c) }

/-- Effect of a list of edits, applied left to right. -/
def applyEdits (p : Policy) (es : List Edit) : Policy := es.foldl applyEdit p

/-- An application manifest. -/
structure Manifest where
  cmd : List String
  roles : List Role
  policy : Policy
  deriving Repr

/-- Canonicalisation of a command line: empty arguments are dropped. -/
def canonCmd (cmd : List String) : List String := cmd.filter (· ≠ "")

/-- Canonicalisation of a role list: deduplicate and order by decreasing privilege. -/
def canonRoles (rs : List Role) : List Role := allRoles.filter (· ∈ rs)

/-- The engine's build pipeline. -/
def build (cmd : List String) (roles : List Role) (p : Policy) : Manifest :=
  { cmd := canonCmd cmd, roles := canonRoles roles, policy := p }

/-- Re-configuring an app: apply the policy edits and re-run the build pipeline. -/
def alterPolicy (m : Manifest) (es : List Edit) : Manifest :=
  build m.cmd m.roles (applyEdits m.policy es)

/-- Well-formed (engine-produced) manifests. -/
structure WF (m : Manifest) : Prop where
  cmd_ne : ∀ a ∈ m.cmd, a ≠ ""
  roles_sub : m.roles.Sublist allRoles

/-! ## Auxiliary lemmas -/

/-- Filtering a duplicate-free list by membership in one of its sublists
recovers exactly that sublist. -/
theorem filter_mem_of_sublist {α : Type u} [DecidableEq α] :
    ∀ {s l : List α}, s.Sublist l → l.Nodup → l.filter (· ∈ s) = s := by
  intro s l h
  induction h with
  | slnil => intro _; simp
  | @cons l₁ l₂ a h ih =>
      intro hnd
      have ha : a ∉ l₂ := (List.nodup_cons.mp hnd).1
      have hnd' : l₂.Nodup := (List.nodup_cons.mp hnd).2
      have has : a ∉ l₁ := fun hx => ha (h.subset hx)
      rw [List.filter_cons_of_neg (by simpa using has), ih hnd']
  | @cons₂ l₁ l₂ a h ih =>
      intro hnd
      have ha : a ∉ l₂ := (List.nodup_cons.mp hnd).1
      have hnd' : l₂.Nodup := (List.nodup_cons.mp hnd).2
      have hcong : l₂.filter (· ∈ a :: l₁) = l₂.filter (· ∈ l₁) := by
        apply List.filter_congr
        intro x hx
        have hxa : x ≠ a := by rintro rfl; exact ha hx
        simp [hxa]
      rw [List.filter_cons_of_pos (by simp), hcong, ih hnd']

theorem canonCmd_eq_self {cmd : List String} (h : ∀ a ∈ cmd, a ≠ "") :
    canonCmd cmd = cmd := by
  unfold canonCmd
  apply List.filter_eq_self.mpr
  intro a ha
  simpa using h a ha

theorem allRoles_nodup : allRoles.Nodup := by decide

theorem canonRoles_eq_self {rs : List Role} (h : rs.Sublist allRoles) :
    canonRoles rs = rs :=
  filter_mem_of_sublist h allRoles_nodup

/-! ## Main theorem -/

/-- **Altering the policy preserves roles and command.**
Re-running the engine's build pipeline after applying an arbitrary list of
policy edits leaves the roles and the command line of a well-formed manifest
untouched (and, of course, installs the edited policy). -/
theorem alter_policy_preserves_roles_and_cmd {m : Manifest} (hm : WF m) (es : List Edit) :
    (alterPolicy m es).roles = m.roles ∧ (alterPolicy m es).cmd = m.cmd := by
  refine ⟨?_, ?_⟩
  · exact canonRoles_eq_self hm.roles_sub
  · exact canonCmd_eq_self hm.cmd_ne

/-- The policy component is exactly the edited policy. -/
theorem alter_policy_policy (m : Manifest) (es : List Edit) :
    (alterPolicy m es).policy = applyEdits m.policy es := rfl

/-- Contrapositive form: if altering the policy changes the roles or the
command line, then the manifest was not engine-produced. -/
theorem not_wf_of_alter_policy_changes {m : Manifest} (es : List Edit)
    (h : (alterPolicy m es).roles ≠ m.roles ∨ (alterPolicy m es).cmd ≠ m.cmd) :
    ¬ WF m := by
  intro hm
  rcases h with h | h
  · exact h (alter_policy_preserves_roles_and_cmd hm es).1
  · exact h (alter_policy_preserves_roles_and_cmd hm es).2

/-- Altering the policy is invisible to any observation that does not look at
the policy: the altered manifest agrees with the original on both remaining
fields simultaneously. -/
theorem alter_policy_eq_with_policy {m : Manifest} (hm : WF m) (es : List Edit) :
    alterPolicy m es = { m with policy := applyEdits m.policy es } := by
  obtain ⟨hr, hc⟩ := alter_policy_preserves_roles_and_cmd hm es
  cases m
  simp_all [alterPolicy, build]

/-! ## Sanity checks: the hypothesis is satisfiable and genuinely needed -/

/-- A concrete well-formed manifest, so the main theorem is not vacuous. -/
example : WF { cmd := ["app", "--safe"], roles := [Role.admin, Role.reader],
               policy := { allowNet := true, allowFS := false, memLimit := 64,
                           denied := ["exec"] } } :=
  ⟨by decide, by decide⟩

/-- Dropping well-formedness, the command line really can change. -/
example :
    (alterPolicy { cmd := ["", "app"], roles := [], policy :=
        { allowNet := false, allowFS := false, memLimit := 0, denied := [] } } []).cmd
      ≠ ["", "app"] := by decide

/-- Dropping well-formedness, the role list really can change. -/
example :
    (alterPolicy { cmd := [], roles := [Role.reader, Role.admin], policy :=
        { allowNet := false, allowFS := false, memLimit := 0, denied := [] } } []).roles
      ≠ [Role.reader, Role.admin] := by decide

#print axioms PCA.Fix.alter_policy_preserves_roles_and_cmd

end PCA.Fix

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

