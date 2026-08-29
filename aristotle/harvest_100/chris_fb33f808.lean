/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

/-!
## Deutsch's algorithm

A two–qubit state is modelled as a vector of complex amplitudes indexed by the
computational basis `Bool × Bool`, i.e. a function `Bool × Bool → ℂ`, where the
first component is the query register and the second the answer register.

The algorithm is:

1. prepare `|0⟩ ⊗ |1⟩`;
2. apply a Hadamard gate to each qubit;
3. make **one** query to the oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`;
4. apply a Hadamard gate to the first qubit;
5. measure the first qubit.

`QC.deutschProb0 f` is the probability that this measurement returns `0`; the
main theorem `QC.deutsch_correct` says that this probability is `1` when `f` is
constant and `0` when `f` is balanced, so a single query decides
constant-vs-balanced with certainty.

Remark on the suggested approach: Mathlib (as of this version) contains no
quantum-computing library — there is no `Hadamard` gate, no quantum oracle and
no notion of measurement probability — so no existing lemma states or closes
this result. The Hilbert-space and `Real.sqrt` API of Mathlib is used
throughout, but the algorithm itself is developed from scratch below.
-/

namespace QC

/-- The sign `(-1)^b` of a bit, as a complex number. -/
noncomputable def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- The normalisation constant `1/√2` of the Hadamard gate. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- Hadamard gate acting on the first qubit:
`H|b⟩ = (|0⟩ + (-1)^b |1⟩)/√2`, applied to the query register. -/
noncomputable def had1 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => invSqrt2 * (psi (false, p.2) + sgn p.1 * psi (true, p.2))

/-- Hadamard gate acting on the second qubit. -/
noncomputable def had2 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => invSqrt2 * (psi (p.1, false) + sgn p.2 * psi (p.1, true))

/-- The phase-kickback-free oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`.
On amplitudes, the amplitude of `|x, y⟩` after the query is the amplitude of
`|x, y ⊕ f x⟩` before it (the map `y ↦ y ⊕ f x` is an involution). -/
def oracleU (f : Bool → Bool) (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The initial state `|0⟩ ⊗ |1⟩`. -/
def initState : Bool × Bool → ℂ := fun p => if p = (false, true) then 1 else 0

/-- The state produced by Deutsch's algorithm just before the measurement:
`(H ⊗ I) U_f (H ⊗ H) |0,1⟩`. Note that `oracleU` occurs exactly once, i.e. the
algorithm makes a single oracle query. -/
noncomputable def deutschState (f : Bool → Bool) : Bool × Bool → ℂ :=
  had1 (oracleU f (had1 (had2 initState)))

/-- The probability that measuring the first qubit of the final state yields
`0`, i.e. the total squared amplitude of the basis states `|0, y⟩`. -/
noncomputable def deutschProb0 (f : Bool → Bool) : ℝ :=
  ∑ y : Bool, ‖deutschState f (false, y)‖ ^ 2

/-- Explicit amplitude of the final state on the basis states `|0, y⟩`:
the interference of the two branches produces the factor `(-1)^{f 0} + (-1)^{f 1}`. -/
theorem deutschState_false (f : Bool → Bool) (y : Bool) :
    deutschState f (false, y) = invSqrt2 ^ 3 * (sgn (f false) + sgn (f true)) * sgn y := by
  simp only [deutschState, had1, had2, oracleU, initState, sgn, invSqrt2]
  cases y <;> cases hf0 : f false <;> cases hf1 : f true <;> simp <;> ring

/-- **Correctness of Deutsch's algorithm.**  With a single query to the oracle
`U_f`, the measurement of the first qubit returns `0` with probability `1` if
`f` is constant (`f 0 = f 1`) and with probability `0` if `f` is balanced
(`f 0 ≠ f 1`). -/
theorem deutsch_correct (f : Bool → Bool) :
    deutschProb0 f = if f false = f true then 1 else 0 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs : |Real.sqrt 2| = Real.sqrt 2 := abs_of_pos h2
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    have h : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    rw [h, hsq]; norm_num
  simp only [deutschProb0, deutschState_false, invSqrt2]
  cases hf0 : f false <;> cases hf1 : f true <;>
    simp [sgn, habs] <;>
    · field_simp
      norm_num
      linarith [h6]

/-- Sanity check on the model: the final state is a genuine unit vector, i.e.
the total measurement probability is `1`. -/
theorem deutschState_normalized (f : Bool → Bool) :
    (∑ p : Bool × Bool, ‖deutschState f p‖ ^ 2) = 1 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have habs : |Real.sqrt 2| = Real.sqrt 2 := abs_of_pos h2
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, deutschState, had1, had2, oracleU, initState, sgn, invSqrt2]
  cases hf0 : f false <;> cases hf1 : f true <;> simp [habs] <;>
    · field_simp
      norm_num

/-- Reformulation: the algorithm accepts (measures `0`) with certainty exactly
when `f` is constant. -/
theorem deutsch_prob0_eq_one_iff (f : Bool → Bool) :
    deutschProb0 f = 1 ↔ f false = f true := by
  rw [deutsch_correct]
  by_cases h : f false = f true <;> simp [h]

/-- Reformulation: the algorithm never measures `0` when `f` is balanced. -/
theorem deutsch_prob0_eq_zero_iff (f : Bool → Bool) :
    deutschProb0 f = 0 ↔ f false ≠ f true := by
  rw [deutsch_correct]
  by_cases h : f false = f true <;> simp [h]

end QC

