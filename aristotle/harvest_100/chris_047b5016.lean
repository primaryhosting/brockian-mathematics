import PCA.Isolation

/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- Resources that a proof-carrying app may touch (files, sockets, ...). -/
abbrev Resource := Nat

/-- A capability set: the resources an app is entitled to touch. -/
abbrev Caps := Resource → Prop

/-- Inclusion of capability sets. -/
def Caps.Sub (S T : Caps) : Prop := ∀ r, S r → T r

/-- Adding one resource to a capability set. -/
def Caps.add (r : Resource) (S : Caps) : Caps := fun x => x = r ∨ S x

/-- Syntax of apps run by the isolation engine.

`grant r` is the *escape hatch*: it is the only construct that lets an app
enlarge its own capability set at run time. -/
inductive Prog where
  | nop
  | access (r : Resource)
  | grant (r : Resource)
  | seq (p q : Prog)
  | choice (p q : Prog)
  | loop (p : Prog)
  deriving Repr, DecidableEq

/-- Run-time semantics: `Run p t` says the app `p` may produce the access
trace `t`.  The engine does **not** dynamically enforce capabilities; isolation
is supposed to come from the certificate alone. -/
inductive Run : Prog → List Resource → Prop
  | nop : Run .nop []
  | access (r : Resource) : Run (.access r) [r]
  | grant (r : Resource) : Run (.grant r) []
  | seq {p q t u} : Run p t → Run q u → Run (.seq p q) (t ++ u)
  | choiceL {p q t} : Run p t → Run (.choice p q) t
  | choiceR {p q t} : Run q t → Run (.choice p q) t
  | loopDone {p} : Run (.loop p) []
  | loopStep {p t u} : Run p t → Run (.loop p) u → Run (.loop p) (t ++ u)

/-- The certificate checker of the isolation engine.
`Certified S p T` means: starting from the capability set `S`, the app `p` is
accepted, with `T` the capability set claimed to hold afterwards.  Subsumption
may enlarge the input capabilities and shrink the claimed output
capabilities. -/
inductive Certified : Caps → Prog → Caps → Prop
  | nop {S} : Certified S .nop S
  | access {S r} : S r → Certified S (.access r) S
  | grant {S r} : Certified S (.grant r) (Caps.add r S)
  | seq {S T U p q} : Certified S p T → Certified T q U → Certified S (.seq p q) U
  | choice {S T p q} : Certified S p T → Certified S q T → Certified S (.choice p q) T
  | loop {S p} : Certified S p S → Certified S (.loop p) S
  | sub {S S' T T' p} : Certified S p T → Caps.Sub S S' → Caps.Sub T' T →
      Certified S' p T'

/-- An app is *clean* when it never uses the `grant` escape hatch. -/
def Clean : Prog → Prop
  | .nop => True
  | .access _ => True
  | .grant _ => False
  | .seq p q => Clean p ∧ Clean q
  | .choice p q => Clean p ∧ Clean q
  | .loop p => Clean p

/-- A trace *escapes* the policy `P` if it touches a resource outside `P`. -/
def Escapes (P : Caps) (t : List Resource) : Prop := ∃ r, r ∈ t ∧ ¬ P r

/-- For a clean app the checker cannot claim any new capability. -/
theorem clean_certified_out_sub {S T : Caps} {p : Prog}
    (hc : Certified S p T) (hcl : Clean p) : Caps.Sub T S := by
  induction hc with
  | nop => exact fun _ h => h
  | access _ => exact fun _ h => h
  | grant => exact hcl.elim
  | seq _ _ ih₁ ih₂ => exact fun r h => ih₁ hcl.1 r (ih₂ hcl.2 r h)
  | choice _ _ ih₁ _ => exact ih₁ hcl.1
  | loop _ _ => exact fun _ h => h
  | sub _ hSS' hTT' ih => exact fun r h => hSS' r (ih hcl r (hTT' r h))

/-- Auxiliary: soundness for a loop, given soundness for its body. -/
theorem run_loop_sub {p : Prog} {S : Caps}
    (hbody : ∀ t, Run p t → ∀ r ∈ t, S r) :
    ∀ t, Run (.loop p) t → ∀ r ∈ t, S r := by
  intro t ht
  generalize hq : Prog.loop p = q at ht
  induction ht with
  | nop => cases hq
  | access r => cases hq
  | grant r => cases hq
  | seq _ _ _ _ => cases hq
  | choiceL _ _ => cases hq
  | choiceR _ _ => cases hq
  | loopDone => exact fun r hr => absurd hr List.not_mem_nil
  | loopStep hb _ _ ih₂ =>
      cases hq
      intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact hbody _ hb r h
      · exact ih₂ rfl r h

/-- **Soundness of the isolation engine on clean apps.**
Every access performed by a certified clean app lies inside the capability set
the certificate started from. -/
theorem clean_certified_run_sub {S T : Caps} {p : Prog}
    (hc : Certified S p T) (hcl : Clean p) :
    ∀ t, Run p t → ∀ r ∈ t, S r := by
  induction hc with
  | nop =>
      intro t ht
      cases ht
      exact fun r hr => absurd hr List.not_mem_nil
  | @access S r hr =>
      intro t ht
      cases ht
      intro s hs
      cases List.mem_singleton.1 hs
      exact hr
  | grant => exact hcl.elim
  | @seq S T U p q hp _ ih₁ ih₂ =>
      intro t ht
      cases ht with
      | seq h₁ h₂ =>
          intro r hr
          rcases List.mem_append.1 hr with h | h
          · exact ih₁ hcl.1 _ h₁ r h
          · exact clean_certified_out_sub hp hcl.1 r (ih₂ hcl.2 _ h₂ r h)
  | choice _ _ ih₁ ih₂ =>
      intro t ht
      cases ht with
      | choiceL h => exact ih₁ hcl.1 _ h
      | choiceR h => exact ih₂ hcl.2 _ h
  | loop _ ih => exact run_loop_sub (ih hcl)
  | sub _ hSS' _ ih =>
      intro t ht r hr
      exact hSS' r (ih hcl t ht r hr)

/-- **Main result.**  There is no clean app that the isolation engine certifies
against a policy and that nevertheless escapes that policy at run time. -/
theorem no_clean_proved_with_escape :
    ¬ ∃ (p : Prog) (P T : Caps) (t : List Resource),
        Clean p ∧ Certified P p T ∧ Run p t ∧ Escapes P t := by
  rintro ⟨p, P, T, t, hcl, hcert, hrun, r, hrt, hrP⟩
  exact hrP (clean_certified_run_sub hcert hcl t hrun r hrt)

/-- Non-vacuity: clean certified apps with a non-empty trace do exist. -/
theorem exists_clean_certified_run :
    ∃ (p : Prog) (P T : Caps) (t : List Resource),
      Clean p ∧ Certified P p T ∧ Run p t ∧ t ≠ [] := by
  refine ⟨.loop (.access 0), fun r => r = 0, fun r => r = 0, [0], trivial,
    Certified.loop (Certified.access rfl), ?_, by simp⟩
  have h := Run.loopStep (Run.access 0) (Run.loopDone (p := .access 0))
  simpa using h

/-- Sharpness: the cleanliness hypothesis cannot be dropped — an app using the
`grant` escape hatch can be certified and still escape its policy. -/
theorem exists_certified_escape_of_grant :
    ∃ (p : Prog) (P T : Caps) (t : List Resource),
      ¬ Clean p ∧ Certified P p T ∧ Run p t ∧ Escapes P t := by
  refine ⟨.seq (.grant 1) (.access 1), fun r => r = 0, Caps.add 1 (fun r => r = 0),
    [1], by simp [Clean], Certified.seq Certified.grant (Certified.access ?_), ?_,
    ⟨1, by simp⟩⟩
  · exact Or.inl rfl
  · have h := Run.seq (Run.grant 1) (Run.access 1)
    simpa using h

end PCA.Isolation

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

