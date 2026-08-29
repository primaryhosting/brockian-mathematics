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

theorem clean_iff (s : Sandbox) (p : Prog) :
    Clean s p ↔ ∀ c : Cap, effects p (Effect.cap c) → s.allowed c = true := by
  unfold Clean
  induction p with
  | skip => simp [scan]
  | use c k ih =>
      simp only [scan, Bool.and_eq_true, ih, effects_use]
      constructor
      · rintro ⟨hc, hk⟩ c' hc'
        rcases hc' with h | h
        · cases h; exact hc
        · exact hk c' h
      · intro h
        exact ⟨h c (Or.inl rfl), fun c' hc' => h c' (Or.inr hc')⟩
  | touch a k ih => simpa [scan] using ih
  | branch t e iht ihe =>
      simp only [scan, Bool.and_eq_true, iht, ihe, effects_branch]
      constructor
      · rintro ⟨h1, h2⟩ c hc; rcases hc with h | h
        · exact h1 c h
        · exact h2 c h
      · intro h
        exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | loop b k ihb ihk =>
      simp only [scan, Bool.and_eq_true, ihb, ihk, effects_loop]
      constructor
      · rintro ⟨h1, h2⟩ c hc; rcases hc with h | h
        · exact h1 c h
        · exact h2 c h
      · intro h
        exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩

/-- A memory-safety certificate exists exactly when every touched address lies
inside the isolated region. -/
