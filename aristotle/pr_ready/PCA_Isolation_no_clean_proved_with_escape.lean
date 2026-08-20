/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
Note on imports: the required header above must be the very first thing in the file, and
Lean forbids any `import` after a leading module doc-comment.  The development below is
therefore carried out in plain Lean 4 core (`Init`), with no Mathlib import; every notion
used (`List`, membership, decidability) is available there.
-/

namespace PCA.Isolation

/-- A capability is an abstract resource token that the isolation engine mediates. -/
abbrev Cap := Nat

/-- An application, described by the list of capabilities it *declares* it will use.
This declaration is what the proof carried by the app talks about. -/
structure App where
  declared : List Cap
  deriving DecidableEq

/-- A sandbox policy, described by the list of capabilities the isolation engine actually
*grants* at run time. -/
structure Policy where
  granted : List Cap
  deriving DecidableEq

/-- An execution trace is the list of capabilities exercised, in order. -/
abbrev Trace := List Cap

/-- A trace is *clean* for an app when every capability it exercises was declared. -/
def Clean (a : App) (t : Trace) : Prop := ∀ c ∈ t, c ∈ a.declared

/-- An app is *proved* against a policy when its carried certificate checks out, i.e. every
declared capability is granted by the policy. -/
def Proved (p : Policy) (a : App) : Prop := ∀ c ∈ a.declared, c ∈ p.granted

/-- A trace *escapes* the sandbox when it exercises some capability that is not granted. -/
def Escapes (p : Policy) (t : Trace) : Prop := ∃ c ∈ t, c ∉ p.granted

/-! ### The engine's checks are effective -/

instance (a : App) (t : Trace) : Decidable (Clean a t) := by
  unfold Clean; infer_instance

instance (p : Policy) (a : App) : Decidable (Proved p a) := by
  unfold Proved; infer_instance

instance (p : Policy) (t : Trace) : Decidable (Escapes p t) := by
  unfold Escapes; infer_instance

/-! ### Soundness of the isolation engine -/

/-- **Main theorem (soundness).** No clean run of a proved app ever escapes the sandbox:
if every capability used was declared, and every declared capability is granted, then no
used capability can be ungranted. -/
theorem no_clean_proved_with_escape
    (p : Policy) (a : App) (t : Trace)
    (hc : Clean a t) (hp : Proved p a) : ¬ Escapes p t := by
  rintro ⟨c, hct, hcg⟩
  exact hcg (hp c (hc c hct))

/-- Predicate-level restatement: no triple `(app, trace)` is simultaneously clean, proved
and escaping. -/
theorem no_clean_proved_escaping_triple (p : Policy) :
    ∀ x : App × Trace, ¬ (Clean x.1 x.2 ∧ Proved p x.1 ∧ Escapes p x.2) := by
  rintro ⟨a, t⟩ ⟨hc, hp, he⟩
  exact no_clean_proved_with_escape p a t hc hp he

/-- Contrapositive form: an escaping run means either the app misbehaved (it used an
undeclared capability) or its certificate does not check out against the policy. -/
theorem escape_imp_not_clean_or_not_proved
    (p : Policy) (a : App) (t : Trace) (he : Escapes p t) :
    ¬ Clean a t ∨ ¬ Proved p a := by
  by_cases hc : Clean a t
  · exact Or.inr fun hp => no_clean_proved_with_escape p a t hc hp he
  · exact Or.inl hc

/-! ### Completeness: both hypotheses are necessary -/

/-- Decidable de Morgan for bounded universal quantification over a list. -/
private theorem exists_not_of_not_forall_mem
    {P : Cap → Prop} [DecidablePred P] :
    ∀ {l : List Cap}, ¬ (∀ c ∈ l, P c) → ∃ c ∈ l, ¬ P c
  | [], h => absurd (by intro c hc; cases hc) h
  | b :: l, h => by
      by_cases hb : P b
      · have h' : ¬ (∀ c ∈ l, P c) := by
          intro hall
          exact h (by
            intro c hc
            cases hc with
            | head => exact hb
            | tail _ hc => exact hall c hc)
        obtain ⟨c, hc, hnc⟩ := exists_not_of_not_forall_mem h'
        exact ⟨c, List.mem_cons_of_mem _ hc, hnc⟩
      · exact ⟨b, List.mem_cons_self .., hb⟩

/-- If an app's certificate fails (some declared capability is not granted) then there is a
*clean* trace of that app which escapes.  Hence the hypothesis `Proved` in the main theorem
cannot be dropped. -/
theorem exists_clean_escape_of_not_proved
    (p : Policy) (a : App) (hp : ¬ Proved p a) :
    ∃ t : Trace, Clean a t ∧ Escapes p t := by
  obtain ⟨c, hcd, hcg⟩ := exists_not_of_not_forall_mem (P := fun c => c ∈ p.granted) hp
  refine ⟨[c], ?_, ⟨c, List.mem_cons_self .., hcg⟩⟩
  intro d hd
  cases hd with
  | head => exact hcd
  | tail _ hd => cases hd

/-- If some capability lies outside the policy then escaping traces exist at all; for a
proved app such a trace is necessarily unclean.  Hence the hypothesis `Clean` in the main
theorem cannot be dropped either. -/
theorem exists_escape_of_ungranted
    (p : Policy) {c : Cap} (hc : c ∉ p.granted) :
    ∃ t : Trace, Escapes p t :=
  ⟨[c], c, List.mem_cons_self .., hc⟩

/-- Full characterisation of sandbox safety for a run: a trace fails to escape exactly when
every capability it exercises is granted. -/
theorem not_escapes_iff (p : Policy) (t : Trace) :
    ¬ Escapes p t ↔ ∀ c ∈ t, c ∈ p.granted := by
  constructor
  · intro h c hct
    by_cases hcg : c ∈ p.granted
    · exact hcg
    · exact absurd ⟨c, hct, hcg⟩ h
  · rintro h ⟨c, hct, hcg⟩
    exact hcg (h c hct)

end PCA.Isolation


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

