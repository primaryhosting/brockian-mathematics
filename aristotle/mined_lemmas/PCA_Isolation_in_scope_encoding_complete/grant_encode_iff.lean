/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- The kind of access a request asks for. -/
inductive Access
  | read
  | write
  deriving DecidableEq, Repr

/-- A request made by an application: a resource path together with an access mode. -/
structure Request where
  path : List String
  access : Access
  deriving DecidableEq, Repr

/-- A capability granted to an application: every resource under `prefixPath` may be read,
and may additionally be written when `mayWrite` is `true`. -/
structure Grant where
  prefixPath : List String
  mayWrite : Bool
  deriving DecidableEq, Repr

/-- Semantic ("model") notion of a grant permitting a request. -/

theorem grant_encode_iff (g : Grant) (r : Request) :
    g.encode r = true ↔ g.Permits r := by
  obtain ⟨p, a⟩ := r
  cases a <;>
    simp [Grant.encode, Grant.Permits, List.isPrefixOf_iff_prefix]

/-- **Completeness of the isolation engine's scope encoding**: every request that is in scope
according to the model is accepted by the executable encoding. -/
