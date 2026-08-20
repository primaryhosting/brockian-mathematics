/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: a Lean module doc comment (`/-! ... -/`) must precede any `import`
command, so this module is deliberately self-contained and uses no imports.  The
`Escalates` relation below is the reflexive-transitive closure of the one-step
escalation relation; it is the analogue of Mathlib's `Relation.ReflTransGen`, and
`PCA.Isolation.Escalates.mono` is the analogue of `Relation.ReflTransGen.mono`,
which is the Mathlib lemma that does the essential work of the target theorem.
-/

namespace PCA.Isolation

universe u

/-- `Escalates g a b` : starting from privilege `a`, the isolation engine's
one-step escalation relation `g` allows reaching privilege `b` in finitely many
steps.  This is the reflexive-transitive closure of `g`. -/
inductive Escalates {P : Type u} (g : P → P → Prop) : P → P → Prop
  | refl (a : P) : Escalates g a a
  | tail {a b c : P} : Escalates g a b → g b c → Escalates g a c

namespace Escalates


theorem escape_closed {P : Type u} {g : P → P → Prop} {S : P → Prop} {x y : P}
    (hx : escape g S x) (hxy : g x y) : escape g S y := by
  obtain ⟨p, hp, hchain⟩ := hx
  exact ⟨p, hp, hchain.tail hxy⟩

/-- Completeness of the model: `escape g S` is the *least* set of privileges that
contains `S` and is closed under one-step escalation.  Hence any invariant an
isolation engine verifies against every escalation step really does hold of every
escapable privilege. -/
