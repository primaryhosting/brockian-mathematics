import Mathlib


def FortuneConjecture : Prop :=
  ∀ n P m : ℕ, P = primorial n → FortunateFor P m → m.Prime

/-- Any Fortunate number `m` for a positive base `P` is coprime to `P`: a common divisor `d`
of `m` and `P` divides the prime `P + m`, and `d ≤ m < P + m`, so `d = 1`. -/
