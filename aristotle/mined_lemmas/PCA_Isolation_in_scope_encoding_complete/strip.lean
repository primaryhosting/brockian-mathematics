/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-- A resource path in the isolation engine's name space: a sequence of name
components (components are interned names, represented by natural numbers). -/
abbrev Path := List Nat

/-- A sandbox of the isolation engine: a `root` (the mount point the sandboxed
app is confined to) together with a deny predicate `denied` that can additionally
block individual absolute paths inside the sandbox. -/
structure Sandbox where
  /-- The mount point the sandboxed application is confined to. -/
  root : Path
  /-- Absolute paths explicitly blocked by the isolation policy. -/
  denied : Path → Bool

/-- A path `p` is *in scope* for sandbox `s` when it lies under the sandbox root,
say `p = s.root ++ c`, and no non-trivial ancestor of `p` below the root is denied. -/

def strip : Path → Path → Option Path
  | [], p => some p
  | _ :: _, [] => none
  | a :: r, b :: p => if a = b then strip r p else none

/-- Walk down the components of a sandbox-relative path, starting from the absolute
path `acc`, failing as soon as one of the traversed absolute paths is denied. -/
