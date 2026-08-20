/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Self-contained development: no external imports are needed, and Lean does not
-- permit `import` after the required module header comment above.

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

/-- An access mode requested by (or granted to) a component of a proof-carrying app. -/
inductive Mode
  | read
  | write
  deriving DecidableEq, Repr

/-- A resource of the isolation engine, identified by a hierarchical path
(e.g. `["home", "user", "data.txt"]`). -/
structure Resource where
  path : List String
  deriving DecidableEq, Repr

/-- A capability grant: every resource sitting under `prefixPath` may be accessed
with mode `mode` (a `write` grant subsumes `read`). -/
structure Grant where
  prefixPath : List String
  mode : Mode
  deriving DecidableEq, Repr

/-- The declarative (specification-level) meaning of a grant: it covers the request
`(m, r)` when its path prefix is a prefix of the resource path and the granted mode
is strong enough for the requested mode. -/

theorem inScope_mono {P Q : Policy} (hPQ : ∀ g, g ∈ P → g ∈ Q) (m : Mode) (r : Resource)
    (h : InScope P m r) : InScope Q m r := by
  obtain ⟨g, hgP, hg⟩ := h
  exact ⟨g, hPQ g hgP, hg⟩

/-- A write permission always entails the corresponding read permission. -/
