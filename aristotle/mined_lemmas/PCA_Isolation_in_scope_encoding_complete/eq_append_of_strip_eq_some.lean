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

theorem eq_append_of_strip_eq_some :
    ∀ (r p q : Path), strip r p = some q → p = r ++ q := by
  intro r
  induction r with
  | nil => intro p q h; simpa [strip] using h
  | cons a r ih =>
      intro p q h
      match p with
      | [] => simp [strip] at h
      | b :: p' =>
          by_cases hab : a = b
          · subst hab
            rw [strip, if_pos rfl] at h
            simpa using ih p' q h
          · rw [strip, if_neg hab] at h
            exact absurd h (by simp)

/-- The scan of a path all of whose non-empty ancestors are allowed succeeds and is
the identity. -/
