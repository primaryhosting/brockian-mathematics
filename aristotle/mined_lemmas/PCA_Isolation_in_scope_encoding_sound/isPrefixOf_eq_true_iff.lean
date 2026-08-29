/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires `import` commands to precede every other
command in a file, including module docstrings.  Since the mandated header
above must be the very first text in the file, this development is written so
that it needs nothing beyond Lean's built-in `Init` library (the prefix API on
lists), and therefore has no `import` line.  The Mathlib-based project settings
of the original template are not needed here.
-/

set_option autoImplicit false

namespace PCA
namespace Isolation

/-- A resource name in the isolation engine's model: a hierarchical path,
given as the list of its segments (e.g. `["home", "user", "docs"]`). -/
abbrev Path : Type := List String

/-- A *scope* of an isolated component: a list of permitted roots (`allow`)
together with a list of forbidden roots (`deny`).  A resource is governed by a
root exactly when the root is a path-prefix of the resource, and denial takes
precedence over permission. -/
structure Scope where
  /-- Roots under which access is granted. -/
  allow : List Path
  /-- Roots under which access is revoked, overriding `allow`. -/
  deny : List Path
  deriving Repr

/-- The declarative (specification-level) meaning of "resource `r` lies in scope `s`":
some allowed root governs `r`, and no denied root governs `r`. -/

theorem isPrefixOf_eq_true_iff (a r : Path) : a.isPrefixOf r = true ↔ a <+: r :=
  List.isPrefixOf_iff_prefix

/-- Failure of the Boolean prefix test means the prefix relation genuinely fails. -/
