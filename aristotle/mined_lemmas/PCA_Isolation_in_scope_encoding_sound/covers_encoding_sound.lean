/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This development needs no Mathlib import: every lemma used
-- (`List.isPrefixOf_iff_prefix`, `List.any_eq_true`, `decidable_of_iff`)
-- is available in the Lean 4 core library, and the required header comment
-- must be the first thing in the file (Lean forbids `import` after a `/-! -/`
-- module docstring).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-! ## The isolation model

A *resource* is identified by a hierarchical path (a list of path components).
A *scope* granted to an application is a path prefix: holding the scope `s`
authorises access to every resource whose path extends `s.root`.

The isolation engine of a proof-carrying app does not reason with the
propositional predicate directly; it evaluates a decidable *encoding*
(a `Bool`-valued function) built from `List.isPrefixOf` / `List.any`.
The theorems below state that this encoding is sound and complete with
respect to the intended semantics. -/

/-- A resource path: a list of hierarchical components. -/
abbrev Path := List String

/-- A capability scope: everything below `root` is authorised. -/
structure Scope where
  root : Path
  deriving DecidableEq

/-- Semantics of a single scope: `s` covers `p` when `s.root` is a prefix of `p`. -/

theorem covers_encoding_sound (s : Scope) (p : Path) :
    s.coversB p = true ↔ s.Covers p :=
  List.isPrefixOf_iff_prefix

/-- **Main theorem.** The isolation engine's boolean encoding of "the requested
resource is in scope" is sound and complete with respect to the intended
semantics: `inScopeB pol p` returns `true` exactly when some granted scope of
the policy covers the requested path.

The proof reduces to `List.any_eq_true` together with the core lemma
`List.isPrefixOf_iff_prefix`. -/
