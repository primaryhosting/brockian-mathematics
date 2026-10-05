import Mathlib


def FortuneConjecture : Prop :=
  ∀ n P m : ℕ, P = primorial n → FortunateFor P m → m.Prime

/-- If `p` is a prime dividing the (positive) base `P`, then `p` cannot divide a
Fortunate number `m` for `P`: otherwise `p ∣ P + m`, forcing `P + m = p ≤ m`,
contradicting `0 < P`. -/
