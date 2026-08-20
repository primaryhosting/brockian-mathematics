/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The wheel modulus of this member of the `GoldbachWheelK2` family. -/

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → 2 ≤ m → n % m ≠ 0

/-- A boolean trial-division test, used to make `IsPrimeNat` efficiently decidable. -/
