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

theorem no_clean_proved_escaping_triple (p : Policy) :
    ∀ x : App × Trace, ¬ (Clean x.1 x.2 ∧ Proved p x.1 ∧ Escapes p x.2) := by
  rintro ⟨a, t⟩ ⟨hc, hp, he⟩
  exact no_clean_proved_with_escape p a t hc hp he

/-- Contrapositive form: an escaping run means either the app misbehaved (it used an
undeclared capability) or its certificate does not check out against the policy. -/
