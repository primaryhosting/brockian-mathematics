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

theorem not_in_scope_of_encoding_false (pol : Policy) (p : Path)
    (h : inScopeB pol p = false) : ¬ InScope pol p := by
  intro hp
  have := (in_scope_encoding_sound pol p).2 hp
  simp [h] at this

/-- The semantic predicate is decidable, with the engine's encoding as decision
procedure. -/
instance (pol : Policy) (p : Path) : Decidable (InScope pol p) :=
  decidable_of_iff _ (in_scope_encoding_sound pol p)

/-- The empty policy grants nothing: total isolation. -/
