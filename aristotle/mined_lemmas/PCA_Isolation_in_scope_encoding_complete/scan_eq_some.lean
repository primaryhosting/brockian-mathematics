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

theorem scan_eq_some (s : Sandbox) :
    ∀ (acc q t : Path), scan s acc q = some t →
      t = q ∧ ∀ q' : Path, q' <+: q → q' ≠ [] → ¬ s.denied (acc ++ q') := by
  intro acc q
  induction q generalizing acc with
  | nil =>
      intro t ht
      refine ⟨by simpa [scan] using ht.symm, ?_⟩
      intro q' hq' hne
      exact absurd (List.prefix_nil.mp hq') hne
  | cons a rest ih =>
      intro t ht
      by_cases ha : s.denied (acc ++ [a])
      · simp [scan, ha] at ht
      · rw [scan, if_neg ha, Option.map_eq_some_iff] at ht
        obtain ⟨t', ht', rfl⟩ := ht
        obtain ⟨rfl, hall⟩ := ih (acc ++ [a]) t' ht'
        refine ⟨rfl, ?_⟩
        intro q' hq' hne
        match q' with
        | [] => exact absurd rfl hne
        | b :: q'' =>
            obtain ⟨rfl, hq''⟩ := List.cons_prefix_cons.mp hq'
            match q'' with
            | [] => simpa using ha
            | d :: q''' =>
                have := hall (d :: q''') hq'' (by simp)
                simpa [List.append_assoc] using this

/-- **In-scope encoding completeness.**  The isolation engine's encoder never rejects a
path that the policy puts in scope: every in-scope absolute path has a capability code,
and decoding that code recovers exactly the original path. -/
