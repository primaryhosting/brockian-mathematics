/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-! ## Arithmetic: an injective pairing function on `Nat` -/

/-- Szudzik-style pairing function. -/

theorem run_mem_outside (a : Artifact) (m : Machine) (x : Nat)
    (hx : a.policy.maxAddr ≤ x) : (run a m).mem x = m.mem x := by
  unfold run
  generalize a.code = l
  induction l generalizing m with
  | nil => rfl
  | cons i is ih => simpa [List.foldl_cons] using (ih (step a.policy m i)).trans
      (step_mem_outside a.policy m i x hx)

/-- The capability trace only ever grows by capabilities allowed by the policy. -/
