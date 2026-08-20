import Mathlib
namespace Brockian.Schur

/-- Bound function for the Ramsey-type induction: `fR k` many integers suffice when the
    differences take at most `k` colours. -/

def fR : ℕ → ℕ
  | 0 => 2
  | (n + 1) => (n + 1) * fR n + 2

