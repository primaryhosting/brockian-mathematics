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

private theorem root_bounds (a b : Nat) :
    rootNat a b * rootNat a b ≤ pairNat a b ∧
      pairNat a b < (rootNat a b + 1) * (rootNat a b + 1) := by
  unfold rootNat pairNat
  by_cases h : a < b
  · simp only [h, if_pos]
    rw [sq_succ]
    omega
  · simp only [h, if_neg, if_false]
    rw [sq_succ]
    omega

