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

