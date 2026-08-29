/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

/-- Operations a proof-carrying app may request on a resource. -/
inductive Op
  | read
  | write
  | exec
  deriving DecidableEq, Repr

/-- A request made by an app: a resource path together with the operation. -/
structure Request where
  path : List String
  op : Op
  deriving DecidableEq, Repr

/-- A capability grant: a scope (a path prefix) and the operations allowed inside it. -/
structure Grant where
  scope : List String
  ops : List Op
  deriving DecidableEq, Repr

/-- An isolation policy is a list of grants. -/
abbrev Policy := List Grant

/-- The isolation engine's decision procedure: a request is permitted iff some
grant of the policy covers its path (as a prefix) and allows its operation. -/

theorem permits_iff_inScope (pol : Policy) (req : Request) :
    permits pol req = true ↔ InScope pol req := by
  simp [permits, InScope, List.any_eq_true]

/-- The isolated (sandbox-side) representation of a request: the capability it is
issued under, the path *relative* to that capability's scope, and the operation.
No absolute path is ever handed to the isolated component. -/
structure Encoded where
  grant : Grant
  rel : List String
  op : Op
  deriving DecidableEq, Repr

/-- The engine decodes an isolated representation back into an absolute request,
re-checking that the capability belongs to the policy and permits the operation. -/
