/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

/-- The Ed25519 group order
`ℓ = 2^252 + 27742317777372353535851937790883648493`,
the (prime) order of the standard base point of `edwards25519`. -/

def cyclicCurve (n : ℕ) : Curve where
  Scalar := ZMod n
  Pt := ZMod n
  sadd := (· + ·)
  sneg := (- ·)
  szero := 0
  smul := (· * ·)
  padd := (· + ·)
  pneg := (- ·)
  pzero := 0
  act := (· * ·)
  B := 1
  padd_assoc := add_assoc
  padd_comm := add_comm
  padd_zero := add_zero
  padd_neg := fun p => add_neg_cancel p
  sadd_neg := fun a => add_neg_cancel a
  act_sadd := fun a b p => add_mul a b p
  act_smul := fun a b p => mul_assoc a b p
  act_szero := fun p => zero_mul p
  base_injective := fun a b h => by simpa using h

/-- The Ed25519-sized instance of the model, with scalars modulo the group order `ell`. -/
