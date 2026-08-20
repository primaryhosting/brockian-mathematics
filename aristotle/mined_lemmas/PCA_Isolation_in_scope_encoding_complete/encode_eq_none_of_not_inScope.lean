/-
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-- A resource the isolation engine may be asked to mediate access to:
a domain (the isolation boundary it lives behind) together with a path inside it. -/
structure Resource where
  domain : String
  path : List String
  deriving DecidableEq, Repr

/-- An isolation scope: a list of permitted domains together with a maximal path depth. -/
structure Scope where
  allowed : List String
  maxDepth : Nat
  deriving Repr

/-- A resource is *in scope* when its domain is permitted and its path is not too deep. -/

theorem encode_eq_none_of_not_inScope (sc : Scope) (r : Resource) (h : ¬ InScope sc r) :
    encode sc r = none := by
  simp [encode, if_neg h]

end Isolation
end PCA

