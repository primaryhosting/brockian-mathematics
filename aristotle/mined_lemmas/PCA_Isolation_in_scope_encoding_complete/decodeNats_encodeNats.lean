/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace PCA.Isolation

/-! ## The model

We model the isolation engine of a proof-carrying app as follows.

* A *capability* (`Cap`) is one of a fixed set of permissions.
* A *resource* (`Resource`) is a path, i.e. a list of interned symbol identifiers.
* A *scope* (`Scope`) grants a list of capabilities on every resource lying under
  a given root path.
* A request `(c, r)` is *in scope* when `c` is granted and `r` lies under the root.

Requests crossing the isolation boundary are serialised to a bitstring by
`encodeReq` (a self-delimiting unary encoding) and the engine's runtime check is
the boolean function `checkToken`, which decodes the bitstring and re-checks the
scope condition.

The two main results are:

* `PCA.Isolation.in_scope_encoding_complete` — *completeness*: every in-scope
  request has its encoding accepted by the runtime check;
* `PCA.Isolation.in_scope_encoding_sound` — *soundness*: the runtime check only
  accepts encodings of in-scope requests.
-/

/-- The capabilities the isolation engine can grant. -/
inductive Cap
  | read
  | write
  | net
  deriving DecidableEq, Repr

/-- Numeric code of a capability, used by the wire format. -/

@[simp] theorem decodeNats_encodeNats (l : List Nat) : decodeNats (encodeNats l) = some l := by
  induction l with
  | nil => rfl
  | cons n ns ih =>
      unfold decodeNats at *
      simp [encodeNats, decodeAux_encodeNat_append n 0 (encodeNats ns), ih]

/-! ## Soundness and completeness of the isolation check -/

/-- **Completeness**: every in-scope request is accepted by the runtime check on
its encoding. -/
