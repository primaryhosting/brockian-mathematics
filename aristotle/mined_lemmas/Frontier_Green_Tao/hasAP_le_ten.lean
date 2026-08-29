import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Finset

/-- `HasAPOfLength S k` says that the set `S` contains a `k`-term arithmetic progression
`a, a + d, …, a + (k-1) d` with positive common difference `d`. -/

theorem hasAP_le_ten {k : ℕ} (hk : k ≤ 10) : HasAPOfLength PrimeSet k :=
  hasAP_ten.mono hk

/-! ### Admissibility of the progression `n, n + M, …, n + (k-1) M` -/

/-- If every prime `≤ k` divides `M`, then the shifts `i * M` (`i < k`) are admissible:
for every prime `p` there is an `n` with `p ∤ n + i * M` for all `i < k`. -/
