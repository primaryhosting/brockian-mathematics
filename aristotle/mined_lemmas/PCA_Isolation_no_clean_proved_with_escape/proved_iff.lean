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

theorem proved_iff (s : Sandbox) (p : Prog) :
    Proved s p ↔ ∀ a : Addr, effects p (Effect.mem a) → a < s.size := by
  unfold Proved
  constructor
  · intro h
    induction h with
    | skip => intro a ha; exact ha.elim
    | use c k _ ih =>
        intro a ha
        rcases ha with h | h
        · exact absurd h (by simp)
        · exact ih a h
    | touch a k hlt _ ih =>
        intro b hb
        rcases hb with h | h
        · cases h; exact hlt
        · exact ih b h
    | branch t e _ _ iht ihe =>
        intro a ha; rcases ha with h | h
        · exact iht a h
        · exact ihe a h
    | loop b k _ _ ihb ihk =>
        intro a ha; rcases ha with h | h
        · exact ihb a h
        · exact ihk a h
  · intro h
    induction p with
    | skip => exact MemSafe.skip
    | use c k ih => exact MemSafe.use c k (ih fun a ha => h a (Or.inr ha))
    | touch a k ih =>
        exact MemSafe.touch a k (h a (Or.inl rfl))
          (ih fun b hb => h b (Or.inr hb))
    | branch t e iht ihe =>
        exact MemSafe.branch t e (iht fun a ha => h a (Or.inl ha))
          (ihe fun a ha => h a (Or.inr ha))
    | loop b k ihb ihk =>
        exact MemSafe.loop b k (ihb fun a ha => h a (Or.inl ha))
          (ihk fun a ha => h a (Or.inr ha))

/-! ## Main results -/

/-- **Soundness of the isolation engine.**  No app is simultaneously clean
(accepted by the capability scanner), proved (carrying a memory-safety
certificate) and able to escape its sandbox. -/
