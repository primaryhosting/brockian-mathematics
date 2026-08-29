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

theorem pairNat_inj {a b c d : Nat} (h : pairNat a b = pairNat c d) : a = c ∧ b = d := by
  have hab := root_bounds a b
  have hcd := root_bounds c d
  have hroot : rootNat a b = rootNat c d :=
    root_unique hab.1 hab.2 (h ▸ hcd.1) (h ▸ hcd.2)
  by_cases h1 : a < b <;> by_cases h2 : c < d
  · simp only [rootNat, if_pos h1, if_pos h2] at hroot
    subst hroot
    simp only [pairNat, if_pos h1, if_pos h2] at h
    omega
  · simp only [rootNat, if_pos h1, if_neg h2] at hroot
    subst hroot
    simp only [pairNat, if_pos h1, if_neg h2] at h
    omega
  · simp only [rootNat, if_neg h1, if_pos h2] at hroot
    subst hroot
    simp only [pairNat, if_neg h1, if_pos h2] at h
    omega
  · simp only [rootNat, if_neg h1, if_neg h2] at hroot
    subst hroot
    simp only [pairNat, if_neg h1, if_neg h2] at h
    omega

/-! ## Injective encoding of lists of naturals -/

/-- Injective encoding of a list of naturals as a single natural number. -/
