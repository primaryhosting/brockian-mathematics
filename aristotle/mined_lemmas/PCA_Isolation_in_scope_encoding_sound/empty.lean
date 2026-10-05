/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- A single component of a resource path (e.g. one segment of `"/etc/ssl/certs"`). -/
abbrev Component := String

/-- The actions an application may attempt on a resource. -/
inductive Action where
  | read : Action
  | write : Action
  | exec : Action
  deriving DecidableEq, Repr

/-- A capability grants `action` on every resource under the path prefix `path`. -/
structure Capability where
  action : Action
  path : List Component
  deriving DecidableEq, Repr

/-- A request made by the application: an `action` on the resource at `path`. -/
structure Request where
  action : Action
  path : List Component
  deriving DecidableEq, Repr

/-- The isolation scope of an application: the list of capabilities it was granted. -/
abbrev Scope := List Capability

/-- Declarative semantics of the isolation engine: a request is *in scope* when some granted
capability matches its action and its path prefixes the requested resource path. -/

def empty : Trie := .node false .nil

end Trie

mutual

/-- `t.accepts r` walks the resource path `r` through the trie `t`, accepting as soon as it
reaches an accepting node. -/
