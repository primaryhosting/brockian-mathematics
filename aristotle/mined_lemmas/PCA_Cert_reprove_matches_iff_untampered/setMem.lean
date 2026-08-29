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

def setMem (mem : Nat → Nat) (a v : Nat) : Nat → Nat := fun x => if x = a then v else mem x

/-- One step of the isolation engine.  Any policy violation traps (sets `fault`)
and has no effect on memory or on the capability trace. -/
