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

theorem scan_eq_self (s : Sandbox) (acc c : Path)
    (h : ∀ c' : Path, c' <+: c → c' ≠ [] → ¬ s.denied (acc ++ c')) :
    scan s acc c = some c := by
  induction c generalizing acc with
  | nil => simp [scan]
  | cons a rest ih =>
      have ha : ¬ s.denied (acc ++ [a]) :=
        h [a] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (by simp)
      have hrest : scan s (acc ++ [a]) rest = some rest := by
        refine ih (acc ++ [a]) ?_
        intro c' hc' hne
        have h2 := h (a :: c') (List.cons_prefix_cons.mpr ⟨rfl, hc'⟩) (by simp)
        simpa [List.append_assoc] using h2
      simp [scan, ha, hrest]

/-- A successful scan is the identity and certifies that every non-empty ancestor of
the scanned path is allowed. -/
