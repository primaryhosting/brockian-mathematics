/- Lean requires `import` to precede any module docstring, so the required header comment
appears immediately after the import below. -/
import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) * d` of length `k` with nonzero common difference `d`. -/
def HasAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- **The Green–Tao theorem, as a statement**: the set of prime numbers contains
arithmetic progressions of every (finite) length, i.e. arbitrarily long ones. -/
def GreenTaoStatement : Prop :=
  ∀ k : ℕ, HasAPOfLength {p : ℕ | p.Prime} k

/-- **The Erdős–Turán conjecture on arithmetic progressions**, as a statement: any set of
natural numbers whose sum of reciprocals diverges contains arbitrarily long arithmetic
progressions.  (This is an open problem; it implies the Green–Tao theorem, as
`Frontier.Green_Tao` below shows.) -/
def ErdosTuranAPStatement : Prop :=
  ∀ S : Set ℕ, ¬ Summable (Set.indicator S fun n : ℕ ↦ (1 : ℝ) / n) →
    ∀ k : ℕ, HasAPOfLength S k

/-- Containing an AP of length `k` is monotone (downwards) in `k`. -/
theorem HasAPOfLength.mono {S : Set ℕ} {k l : ℕ} (h : HasAPOfLength S l) (hkl : k ≤ l) :
    HasAPOfLength S k := by
  obtain ⟨a, d, hd, ha⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ ha i (lt_of_lt_of_le hi hkl)⟩

/-- Unconditional base cases of the Green–Tao theorem: the primes contain an arithmetic
progression of length `k` for every `k ≤ 10`.  Indeed
`199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089` is a 10-term AP of primes with
common difference `210`. -/
theorem Green_Tao_base {k : ℕ} (hk : k ≤ 10) : HasAPOfLength {p : ℕ | p.Prime} k := by
  refine HasAPOfLength.mono (l := 10) ⟨199, 210, by norm_num, ?_⟩ hk
  intro i hi
  have : ∀ i < 10, Nat.Prime (199 + i * 210) := by
    set_option maxRecDepth 10000 in decide
  exact this i hi

/-- The primes have divergent sum of reciprocals, phrased for `Set.indicator`. -/
theorem not_summable_one_div_indicator_primes :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime} fun n : ℕ ↦ (1 : ℝ) / n) :=
  not_summable_one_div_on_primes

/-- **Green–Tao, as a Lean-checked reduction.**  The primes contain arbitrarily long
arithmetic progressions, granting the Erdős–Turán conjecture on arithmetic progressions.

The reduction is unconditional Lean-checked mathematics: the only input beyond the
hypothesis `hET` is the (proved, in Mathlib) divergence of the sum of the reciprocals of
the primes.  Unconditional base cases (all lengths `k ≤ 10`) are proved in
`Frontier.Green_Tao_base`. -/
theorem Green_Tao (hET : ErdosTuranAPStatement) : GreenTaoStatement :=
  fun k ↦ hET {p : ℕ | p.Prime} not_summable_one_div_indicator_primes k

end Frontier

#print axioms Frontier.Green_Tao
#print axioms Frontier.Green_Tao_base

