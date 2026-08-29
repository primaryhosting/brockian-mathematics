/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Formalizing the statement -/

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with nonzero common difference `d`. -/

def ErdosTuranAP : Prop :=
  ∀ S : Set ℕ, ¬ Summable (Set.indicator S fun n : ℕ => (1 : ℝ) / n) →
    ContainsArbitrarilyLongAPs S

/-- Dickson's conjecture (for linear forms with natural number coefficients): if the linear
forms `a i + b i * n` (`i < k`, `b i > 0`) are *admissible*, i.e. for every prime `p` there is
an `n` making none of the values divisible by `p`, then there are arbitrarily large `n` at
which all `k` forms are simultaneously prime. -/
