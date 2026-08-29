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

def effects : Prog → Effect → Prop
  | .skip, _ => False
  | .use c k, e => e = Effect.cap c ∨ effects k e
  | .touch a k, e => e = Effect.mem a ∨ effects k e
  | .branch t e', e => effects t e ∨ effects e' e
  | .loop b k, e => effects b e ∨ effects k e

/-- Small-step operational semantics, labelled by the emitted effect. -/
inductive Step : Prog → Option Effect → Prog → Prop
  | use (c k) : Step (.use c k) (some (.cap c)) k
  | touch (a k) : Step (.touch a k) (some (.mem a)) k
  | branchL (t e) : Step (.branch t e) none t
  | branchR (t e) : Step (.branch t e) none e
  | loopIter (b k) : Step (.loop b k) none (b.append (.loop b k))
  | loopExit (b k) : Step (.loop b k) none k

/-- Reachability in the operational semantics (labels forgotten). -/
inductive Steps : Prog → Prog → Prop
  | refl (p) : Steps p p
  | head {p q r : Prog} {o : Option Effect} : Step p o q → Steps q r → Steps p r

/-- `Emits p e` : some configuration reachable from `p` emits the effect `e`. -/
