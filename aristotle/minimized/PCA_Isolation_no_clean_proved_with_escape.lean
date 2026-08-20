/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
