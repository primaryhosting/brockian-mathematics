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

theorem encode_injOn (sc : Scope) {r₁ r₂ : Resource} {c : List String}
    (h₁ : encode sc r₁ = some c) (h₂ : encode sc r₂ = some c) : r₁ = r₂ := by
  have d₁ := decode_encode sc r₁ c h₁
  have d₂ := decode_encode sc r₂ c h₂
  have : some r₁ = some r₂ := d₁ ▸ d₂ ▸ rfl
  exact Option.some.inj this

/-- Out-of-scope resources have no encoding. -/
