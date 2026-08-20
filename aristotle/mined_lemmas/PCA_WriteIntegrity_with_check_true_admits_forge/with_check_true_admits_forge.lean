/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which must be the very
-- first command in the file; Lean therefore forbids any `import` after it. The development
-- below is consequently written against the Lean 4 core library only (no Mathlib lemmas are
-- needed: the goals are closed by `rfl`, `simp` and `omega`, all available in core).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: it targets a memory `region`,
carries a `payload`, and presents a capability certificate `cert` that is supposed to
witness the writer's authority over that region. -/
structure Write where
  region : Nat
  payload : Nat
  cert : Nat
  deriving DecidableEq

/-- `key r` is the capability token authorizing writes to region `r`.
A write is *authentic* exactly when the certificate it presents is the region's token. -/

theorem with_check_true_admits_forge (key : Nat → Nat) :
    (∃ w : Write, Forges key (fun _ => true) w) ∧ ¬ Sound key (fun _ => true) := by
  have hforge : Forges key (fun _ => true) ⟨0, 0, key 0 + 1⟩ := by
    refine ⟨rfl, ?_⟩
    intro h
    simp only [Authentic] at h
    omega
  refine ⟨⟨_, hforge⟩, ?_⟩
  intro hs
  exact hforge.2 (hs _ hforge.1)

end PCA.WriteIntegrity

#print axioms PCA.WriteIntegrity.with_check_true_admits_forge

