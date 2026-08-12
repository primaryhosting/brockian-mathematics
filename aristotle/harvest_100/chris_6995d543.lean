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
# A formal model of a policy-controlled isolation engine (`PCA`)

This file develops a small but complete formal model of an *isolation engine*:
a component that decides whether a command may be executed on behalf of a set of
roles under a capability policy, and, if so, produces the sandbox in which the
command is to be run.

The main results are

* `PCA.run_allow_iff` : soundness **and** completeness of the engine with respect
  to the declarative specification `PCA.Permits`;
* `PCA.run_sound`, `PCA.run_complete`, `PCA.run_deny_iff` : the two directions and
  the corresponding characterisation of denials;
* `PCA.allow_least_privilege` : the produced sandbox carries exactly the
  capabilities the command needs, and every one of them is actually granted;
* `PCA.run_congr` : the verdict only depends on the grants for the roles of the
  request and the capabilities needed by the command (an isolation / non-interference
  property);
* `PCA.Fix.alter_policy_preserves_roles_and_cmd` and the surrounding lemmas: the
  policy-repair operation changes nothing but the policy, only ever adds grants,
  adds only grants that are needed, and does repair the request.
-/

namespace PCA

/-- Capabilities that a command may require and a policy may grant. -/
inductive Cap where
  | read | write | net | exec
  deriving DecidableEq, Repr

/-- Principals are identified by a numeric role identifier. -/
abbrev Role := ℕ

/-- A policy records, for every role and capability, whether the capability is granted. -/
structure Policy where
  grants : Role → Cap → Bool

/-- A policy `p` is weaker than `q` if every grant of `p` is also a grant of `q`. -/
def Policy.le (p q : Policy) : Prop := ∀ ρ c, p.grants ρ c = true → q.grants ρ c = true

/-- A command, together with the capabilities it needs in order to run. -/
structure Cmd where
  name : String
  needs : List Cap
  deriving DecidableEq, Repr

/-- A request to the engine: the roles of the caller, the command, and the policy in force. -/
structure Request where
  roles : List Role
  cmd : Cmd
  policy : Policy

/-- The isolated environment a command is executed in: the capabilities handed to it. -/
structure Sandbox where
  caps : List Cap
  deriving DecidableEq, Repr

/-- The possible answers of the engine. -/
inductive Verdict where
  | allow (s : Sandbox)
  | deny (missing : Cap)
  deriving DecidableEq, Repr

/-- A capability is granted to a request when some role of the caller has it. -/
def Request.granted (r : Request) (c : Cap) : Bool :=
  r.roles.any (fun ρ => r.policy.grants ρ c)

/-- Declarative specification: the request is admissible when every needed capability
is granted to one of the caller's roles. -/
def Permits (r : Request) : Prop := ∀ c ∈ r.cmd.needs, r.granted c = true

instance (r : Request) : Decidable (Permits r) := by
  unfold Permits; infer_instance

/-- The isolation engine. It scans the needed capabilities; the first one that is not
granted causes a denial, otherwise the command is admitted into a sandbox carrying
exactly the needed capabilities. -/
def run (r : Request) : Verdict :=
  match r.cmd.needs.find? (fun c => !r.granted c) with
  | some c => .deny c
  | none => .allow ⟨r.cmd.needs⟩

/-- **Soundness**: an `allow` verdict really does witness admissibility, and the sandbox
produced is the one determined by the command. -/
theorem run_sound {r : Request} {s : Sandbox} (h : run r = .allow s) :
    Permits r ∧ s.caps = r.cmd.needs := by
  unfold run at h
  cases hf : r.cmd.needs.find? (fun c => !r.granted c) with
  | some c => rw [hf] at h; exact absurd h (by simp)
  | none =>
      rw [hf] at h
      have hs : s = ⟨r.cmd.needs⟩ := by
        cases h; rfl
      refine ⟨?_, by rw [hs]⟩
      intro c hc
      have := List.find?_eq_none.mp hf c hc
      simpa using this

/-- **Completeness**: every admissible request is allowed, with the expected sandbox. -/
theorem run_complete {r : Request} (h : Permits r) : run r = .allow ⟨r.cmd.needs⟩ := by
  unfold run
  have hf : r.cmd.needs.find? (fun c => !r.granted c) = none := by
    refine List.find?_eq_none.mpr ?_
    intro c hc
    simp [h c hc]
  rw [hf]

/-- Soundness and completeness combined. -/
theorem run_allow_iff (r : Request) : run r = .allow ⟨r.cmd.needs⟩ ↔ Permits r :=
  ⟨fun h => (run_sound h).1, run_complete⟩

/-- The engine is total and unambiguous: it allows iff it does not deny. -/
theorem run_deny_iff (r : Request) : (∃ c, run r = .deny c) ↔ ¬ Permits r := by
  constructor
  · rintro ⟨c, hc⟩ hp
    rw [run_complete hp] at hc
    exact absurd hc (by simp)
  · intro hp
    unfold run
    cases hf : r.cmd.needs.find? (fun c => !r.granted c) with
    | some c => exact ⟨c, rfl⟩
    | none =>
        exact absurd (fun c hc => by simpa using List.find?_eq_none.mp hf c hc) hp

/-- A denial always names a capability that the command genuinely needs and that the
caller genuinely lacks. -/
theorem run_deny_witness {r : Request} {c : Cap} (h : run r = .deny c) :
    c ∈ r.cmd.needs ∧ r.granted c = false := by
  unfold run at h
  cases hf : r.cmd.needs.find? (fun c => !r.granted c) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some d =>
      rw [hf] at h
      have hcd : d = c := by cases h; rfl
      subst hcd
      exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- **Least privilege**: the sandbox of an allowed request contains exactly the
capabilities the command needs, and each of them is granted by the policy. -/
theorem allow_least_privilege {r : Request} {s : Sandbox} (h : run r = .allow s) :
    (∀ c ∈ s.caps, c ∈ r.cmd.needs ∧ r.granted c = true) ∧
      (∀ c ∈ r.cmd.needs, c ∈ s.caps) := by
  obtain ⟨hp, hs⟩ := run_sound h
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rw [hs] at hc; exact ⟨hc, hp c hc⟩
  · rw [hs]; exact hc

private theorem find?_congr_on {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
      have ha : p a = q a := h a (by simp)
      simp only [List.find?_cons, ha]
      cases q a with
      | true => rfl
      | false =>
          simpa using find?_congr_on p q l (fun b hb => h b (by simp [hb]))

/-- **Isolation / non-interference**: the verdict depends only on the grants concerning
the roles of the caller and the capabilities needed by the command. Grants for other
roles or other capabilities cannot influence the engine. -/
theorem run_congr {r₁ r₂ : Request} (hroles : r₁.roles = r₂.roles) (hcmd : r₁.cmd = r₂.cmd)
    (hgrants : ∀ ρ ∈ r₁.roles, ∀ c ∈ r₁.cmd.needs,
      r₁.policy.grants ρ c = r₂.policy.grants ρ c) :
    run r₁ = run r₂ := by
  have hg : ∀ c ∈ r₁.cmd.needs, r₁.granted c = r₂.granted c := by
    intro c hc
    unfold Request.granted
    rw [← hroles]
    refine Bool.eq_iff_iff.mpr ?_
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨ρ, hρ, hg⟩
      exact ⟨ρ, hρ, by rwa [← hgrants ρ hρ c hc]⟩
    · rintro ⟨ρ, hρ, hg⟩
      exact ⟨ρ, hρ, by rwa [hgrants ρ hρ c hc]⟩
  unfold run
  rw [hcmd] at hg ⊢
  rw [find?_congr_on _ _ _ (fun c hc => by rw [hg c hc])]

namespace Fix

/-- Repairing a denied request: grant the role `ρ` exactly the capabilities the command
needs, leaving the roles and the command untouched. -/
def alter_policy (r : Request) (ρ : Role) : Request :=
  { r with
    policy := ⟨fun σ c => r.policy.grants σ c || (decide (σ = ρ) && decide (c ∈ r.cmd.needs))⟩ }

/-- The repair operation touches only the policy: the caller's roles and the command
are preserved. -/
theorem alter_policy_preserves_roles_and_cmd (r : Request) (ρ : Role) :
    (alter_policy r ρ).roles = r.roles ∧ (alter_policy r ρ).cmd = r.cmd :=
  ⟨rfl, rfl⟩

/-- The repair operation is monotone: it never revokes a grant. -/
theorem alter_policy_monotone (r : Request) (ρ : Role) :
    r.policy.le (alter_policy r ρ).policy := by
  intro σ c hc
  simp [alter_policy, hc]

/-- The repair operation is minimal: any new grant is a needed capability handed to `ρ`. -/
theorem alter_policy_minimal (r : Request) (ρ : Role) {σ : Role} {c : Cap}
    (h : (alter_policy r ρ).policy.grants σ c = true) :
    r.policy.grants σ c = true ∨ (σ = ρ ∧ c ∈ r.cmd.needs) := by
  simp only [alter_policy, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- The repair works: after granting the capabilities to a role the caller actually has,
the request is admissible. -/
theorem alter_policy_permits (r : Request) {ρ : Role} (hρ : ρ ∈ r.roles) :
    Permits (alter_policy r ρ) := by
  intro c hc
  have hc' : c ∈ r.cmd.needs := hc
  unfold Request.granted
  refine List.any_eq_true.mpr ⟨ρ, hρ, ?_⟩
  simp [alter_policy, hc']

/-- Consequently, the repaired request is allowed by the engine, in the sandbox
determined by the (unchanged) command. -/
theorem alter_policy_run (r : Request) {ρ : Role} (hρ : ρ ∈ r.roles) :
    run (alter_policy r ρ) = .allow ⟨r.cmd.needs⟩ :=
  run_complete (alter_policy_permits r hρ)

end Fix

end PCA

