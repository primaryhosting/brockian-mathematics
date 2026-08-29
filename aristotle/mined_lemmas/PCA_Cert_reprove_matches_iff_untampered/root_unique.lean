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

private theorem root_unique {v r s : Nat} (hr1 : r * r ≤ v) (hr2 : v < (r + 1) * (r + 1))
    (hs1 : s * s ≤ v) (hs2 : v < (s + 1) * (s + 1)) : r = s := by
  rcases Nat.lt_trichotomy r s with h | h | h
  · exact absurd (Nat.lt_of_lt_of_le hr2 (Nat.mul_le_mul h h)) (Nat.not_lt.2 hs1)
  · exact h
  · exact absurd (Nat.lt_of_lt_of_le hs2 (Nat.mul_le_mul h h)) (Nat.not_lt.2 hr1)

