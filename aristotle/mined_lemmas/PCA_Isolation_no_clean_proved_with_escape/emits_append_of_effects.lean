/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The isolation engine's model

A proof-carrying app is modelled as a small nondeterministic program `Prog`.
Running it emits *effects*: either the exercise of a capability (`Effect.cap`)
or the touching of a memory address (`Effect.mem`).

A `Sandbox` fixes which capabilities are granted and how large the isolated
memory region is.  An app *escapes* the sandbox if some reachable configuration
of its small-step operational semantics emits an effect the sandbox does not
permit.

The engine certifies apps in two independent ways:

* a **static capability scan** (`Clean`), a decidable syntactic check, and
* a **memory-safety certificate** (`Proved`), an inductive derivation shipped
  with the app.

The target theorem `no_clean_proved_with_escape` is the *soundness* of this
certification: no app can be clean, proved and still escape.  The converse,
`clean_and_proved_of_not_escapes`, is its *completeness*: every non-escaping
app is accepted by both certificates.  Both certificates are load-bearing and
the statement is non-vacuous; see the examples at the end of the file.

The development is self-contained (no imports), so that the file can begin with
the required header comment.
-/

namespace PCA
namespace Isolation

/-- Capabilities that an app may exercise. -/
inductive Cap
  | read
  | write
  | net
  | exec
  | spawnProc
  deriving DecidableEq, Repr

/-- Memory addresses. -/
abbrev Addr := Nat

/-- Observable effects of a single execution step. -/
inductive Effect
  | cap (c : Cap)
  | mem (a : Addr)
  deriving DecidableEq, Repr

/-- A sandbox: the granted capabilities and the size of the isolated region. -/
structure Sandbox where
  /-- Which capabilities the sandbox grants. -/
  allowed : Cap → Bool
  /-- The size of the isolated memory region: addresses `< size` are internal. -/
  size : Nat

/-- The effects a sandbox permits. -/

theorem emits_append_of_effects (e : Effect) :
    ∀ (p q : Prog), effects p e → Emits (p.append q) e := by
  intro p
  induction p with
  | skip => intro q h; exact h.elim
  | use c k ih =>
      intro q h
      rcases h with h | h
      · subst h
        exact ⟨_, _, Steps.refl _, Step.use c (k.append q)⟩
      · exact Emits.of_step (Step.use c (k.append q)) (ih q h)
  | touch a k ih =>
      intro q h
      rcases h with h | h
      · subst h
        exact ⟨_, _, Steps.refl _, Step.touch a (k.append q)⟩
      · exact Emits.of_step (Step.touch a (k.append q)) (ih q h)
  | branch t e' iht ihe =>
      intro q h
      rcases h with h | h
      · exact Emits.of_step (Step.branchL (t.append q) (e'.append q)) (iht q h)
      · exact Emits.of_step (Step.branchR (t.append q) (e'.append q)) (ihe q h)
  | loop b k ihb ihk =>
      intro q h
      rcases h with h | h
      · exact Emits.of_step (Step.loopIter b (k.append q))
          (ihb (.loop b (k.append q)) h)
      · exact Emits.of_step (Step.loopExit b (k.append q)) (ihk q h)

/-- **Completeness of the static effect analysis**: every syntactically
occurring effect really is emitted by some run. -/
