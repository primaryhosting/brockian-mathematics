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
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Fix

/-! ## The isolation engine's model

An *app* is a tree of isolation scopes.  Each internal node carries a *policy*, which
restricts the ambient authority available to the subtree below it; each leaf carries a
*request*, consisting of the role under which the leaf runs and the command it wishes to
issue.  The isolation engine permits an app under an ambient policy exactly when every leaf
request is allowed by the ambient policy conjoined with all the policies guarding it. -/

/-- A role identifier. -/
abbrev Role := Nat

/-- A command identifier. -/
abbrev Cmd := Nat

/-- A request: a command issued under a given role. -/
structure Req where
  role : Role
  cmd : Cmd
  deriving DecidableEq

/-- A policy decides, for each role/command pair, whether the command is allowed. -/
abbrev Policy := Role → Cmd → Bool

/-- The always-permissive policy. -/
def Policy.top : Policy := fun _ _ => true

/-- Conjunction (intersection) of two policies: both must allow. -/
def Policy.inter (p q : Policy) : Policy := fun ro cm => p ro cm && q ro cm

/-- `Policy.Le p q` says that `p` is at least as restrictive as `q`. -/
def Policy.Le (p q : Policy) : Prop := ∀ ro cm, p ro cm = true → q ro cm = true

theorem Policy.inter_assoc (p q r : Policy) :
    Policy.inter (Policy.inter p q) r = Policy.inter p (Policy.inter q r) := by
  funext ro cm
  simp [Policy.inter, Bool.and_assoc]

@[simp] theorem Policy.inter_top (p : Policy) : Policy.inter p Policy.top = p := by
  funext ro cm
  simp [Policy.inter, Policy.top]

/-- An app: a tree of isolation scopes with requests at the leaves. -/
inductive App where
  | leaf (r : Req) : App
  | node (p : Policy) (cs : List App) : App

namespace App

/-- Structural induction principle for `App`.  (`App` is a nested inductive type, so this is
derived by hand from the raw recursor.) -/
@[elab_as_elim]
theorem rec_on_children {motive : App → Prop}
    (leaf : ∀ r, motive (.leaf r))
    (node : ∀ p cs, (∀ c ∈ cs, motive c) → motive (.node p cs)) :
    ∀ a, motive a := by
  intro a
  refine App.rec (motive_1 := motive) (motive_2 := fun cs => ∀ c ∈ cs, motive c)
    leaf (fun p cs ih => node p cs ih) (by simp) ?_ a
  intro hd tl ihd ihtl c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ihd
  · exact ihtl c hc

/-- The list of requests occurring in an app, in order. -/
def reqs : App → List Req
  | .leaf r => [r]
  | .node _ cs => (cs.map reqs).flatten

/-- The roles occurring in an app, in order. -/
def roles (a : App) : List Role := a.reqs.map Req.role

/-- The commands occurring in an app, in order. -/
def cmds (a : App) : List Cmd := a.reqs.map Req.cmd

/-- Rewrite every policy in the app with `f`, leaving the tree shape and all requests alone. -/
def alterPolicy (f : Policy → Policy) : App → App
  | .leaf r => .leaf r
  | .node p cs => .node (f p) (cs.map (alterPolicy f))

mutual
/-- The isolation engine.  `permits amb a` is true iff every request in `a` is allowed by the
ambient policy `amb` intersected with all the scope policies enclosing that request. -/
def permits (amb : Policy) : App → Bool
  | .leaf r => amb r.role r.cmd
  | .node p cs => permitsAll (Policy.inter amb p) cs

/-- `permitsAll amb cs` is true iff the engine permits every app in `cs` under `amb`. -/
def permitsAll (amb : Policy) : List App → Bool
  | [] => true
  | c :: cs => permits amb c && permitsAll amb cs
end

/-- The requests of an app, each paired with the conjunction of the policies guarding it. -/
def guards : App → List (Req × Policy)
  | .leaf r => [(r, Policy.top)]
  | .node p cs => ((cs.map guards).flatten).map (fun q => (q.1, Policy.inter p q.2))

@[simp] theorem alterPolicy_leaf (f : Policy → Policy) (r : Req) :
    alterPolicy f (.leaf r) = .leaf r := by
  simp [alterPolicy]

@[simp] theorem alterPolicy_node (f : Policy → Policy) (p : Policy) (cs : List App) :
    alterPolicy f (.node p cs) = .node (f p) (cs.map (alterPolicy f)) := by
  simp [alterPolicy]

@[simp] theorem reqs_leaf (r : Req) : reqs (.leaf r) = [r] := by
  simp [reqs]

@[simp] theorem reqs_node (p : Policy) (cs : List App) :
    reqs (.node p cs) = (cs.map reqs).flatten := by
  simp [reqs]

@[simp] theorem permits_leaf (amb : Policy) (r : Req) :
    permits amb (.leaf r) = amb r.role r.cmd := by
  simp [permits]

@[simp] theorem permits_node (amb p : Policy) (cs : List App) :
    permits amb (.node p cs) = permitsAll (Policy.inter amb p) cs := by
  simp [permits]

@[simp] theorem permitsAll_nil (amb : Policy) : permitsAll amb [] = true := by
  simp [permitsAll]

@[simp] theorem permitsAll_cons (amb : Policy) (c : App) (cs : List App) :
    permitsAll amb (c :: cs) = (permits amb c && permitsAll amb cs) := by
  simp [permitsAll]

@[simp] theorem guards_leaf (r : Req) : guards (.leaf r) = [(r, Policy.top)] := by
  simp [guards]

@[simp] theorem guards_node (p : Policy) (cs : List App) :
    guards (.node p cs) =
      ((cs.map guards).flatten).map (fun q => (q.1, Policy.inter p q.2)) := by
  simp [guards]

/-- `permitsAll` is the pointwise version of `permits`. -/
theorem permitsAll_eq_true_iff (amb : Policy) (cs : List App) :
    permitsAll amb cs = true ↔ ∀ c ∈ cs, permits amb c = true := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-! ## Soundness and completeness of the isolation engine -/

/-- **Soundness and completeness.**  The engine permits an app under an ambient policy exactly
when, for every request of the app, the ambient policy conjoined with the guards enclosing
that request allows it. -/
theorem permits_eq_true_iff (amb : Policy) (a : App) :
    permits amb a = true ↔
      ∀ q ∈ guards a, Policy.inter amb q.2 q.1.role q.1.cmd = true := by
  induction a using App.rec_on_children generalizing amb with
  | leaf r => simp
  | node p cs ih =>
      simp only [permits_node, guards_node, permitsAll_eq_true_iff, List.mem_map,
        List.mem_flatten]
      constructor
      · rintro h q ⟨q', ⟨l, ⟨c, hc, rfl⟩, hq'⟩, rfl⟩
        have := (ih c hc (Policy.inter amb p)).mp (h c hc) q' hq'
        simpa [Policy.inter_assoc] using this
      · intro h c hc
        refine (ih c hc (Policy.inter amb p)).mpr ?_
        rintro q' hq'
        have := h (q'.1, Policy.inter p q'.2)
          ⟨q', ⟨guards c, ⟨c, hc, rfl⟩, hq'⟩, rfl⟩
        simpa [Policy.inter_assoc] using this

/-- Monotonicity: relaxing the ambient policy can only permit more. -/
theorem permits_mono {amb amb' : Policy} (h : Policy.Le amb amb') (a : App)
    (ha : permits amb a = true) : permits amb' a = true := by
  refine (permits_eq_true_iff amb' a).mpr ?_
  intro q hq
  have hq' := (permits_eq_true_iff amb a).mp ha q hq
  simp only [Policy.inter, Bool.and_eq_true] at hq' ⊢
  exact ⟨h _ _ hq'.1, hq'.2⟩

/-- Tightening every policy of an app can only reduce what the engine permits: if the altered
app is permitted, so is the original, provided `f` only ever restricts. -/
theorem permits_of_permits_alterPolicy {f : Policy → Policy}
    (hf : ∀ p, Policy.Le (f p) p) (amb : Policy) (a : App)
    (h : permits amb (alterPolicy f a) = true) : permits amb a = true := by
  induction a using App.rec_on_children generalizing amb with
  | leaf r => simpa using h
  | node p cs ih =>
      simp only [alterPolicy_node, permits_node, permitsAll_eq_true_iff, List.mem_map,
        forall_exists_index, and_imp] at h ⊢
      intro c hc
      refine ih c hc _ ?_
      refine permits_mono (amb := Policy.inter amb (f p)) ?_ _ (h _ c hc rfl)
      intro ro cm hro
      simp only [Policy.inter, Bool.and_eq_true] at hro ⊢
      exact ⟨hro.1, hf p ro cm hro.2⟩

/-- Altering the policies of an app leaves its requests untouched. -/
theorem reqs_alterPolicy (f : Policy → Policy) (a : App) :
    reqs (alterPolicy f a) = reqs a := by
  induction a using App.rec_on_children with
  | leaf r => simp
  | node p cs ih =>
      simp only [alterPolicy_node, reqs_node, List.map_map]
      congr 1
      exact List.map_congr_left (fun c hc => by simpa using ih c hc)

end App

/-- **Main theorem.**  Rewriting the policies of an app preserves the roles and the commands of
all of its requests: the isolation engine's policy layer can change what an app is allowed to
do, but never what it asks to do. -/
theorem alter_policy_preserves_roles_and_cmd (f : Policy → Policy) (a : App) :
    (App.alterPolicy f a).roles = a.roles ∧ (App.alterPolicy f a).cmds = a.cmds := by
  constructor <;> simp [App.roles, App.cmds, App.reqs_alterPolicy]

end PCA.Fix

