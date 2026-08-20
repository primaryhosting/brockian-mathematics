import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header block above
-- appears immediately after the single `import Mathlib` line.)

set_option maxRecDepth 10000

namespace Frontier

/-- `IsPrimeAP k a d` says that `a, a + d, …, a + (k-1) d` is an arithmetic progression of
length `k` consisting of prime numbers, with positive common difference `d`. -/

def GreenTaoConclusion : Prop := ∀ k : ℕ, ∃ a d : ℕ, IsPrimeAP k a d

/-- Dickson's conjecture (in the form used here): given `k` linear forms
`n ↦ a i + b i * n` with positive leading coefficients, if the family is *admissible*,
i.e. for every prime `p` there is some `n` for which no form is divisible by `p`,
then there are arbitrarily large `n` at which all the forms take prime values. -/
