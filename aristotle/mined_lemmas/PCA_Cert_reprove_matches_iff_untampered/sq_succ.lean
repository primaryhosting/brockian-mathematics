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

private theorem sq_succ (n : Nat) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  simp [Nat.mul_add, Nat.add_mul]
  omega

/-- The "root" of a pair: the unique `r` with `r*r ≤ pairNat a b < (r+1)*(r+1)`. -/
