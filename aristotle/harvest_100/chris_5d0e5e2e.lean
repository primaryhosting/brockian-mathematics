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

namespace QC

/-- The sign `(-1)^b` of a bit, as a complex number. -/
noncomputable def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- A two-qubit state, given by its amplitudes on the computational basis
`{|x, y⟩ : x, y ∈ {0,1}}`. -/
abbrev State := Bool × Bool → ℂ

/-- The Hadamard gate `H = (1/√2) • ![![1, 1], ![1, -1]]` applied to the first qubit. -/
noncomputable def had₁ (ψ : State) : State :=
  fun p => ((Real.sqrt 2)⁻¹ : ℝ) * (ψ (false, p.2) + sgn p.1 * ψ (true, p.2))

/-- The Hadamard gate applied to the second qubit. -/
noncomputable def had₂ (ψ : State) : State :=
  fun p => ((Real.sqrt 2)⁻¹ : ℝ) * (ψ (p.1, false) + sgn p.2 * ψ (p.1, true))

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`, described by its action on amplitudes. -/
def oracle (f : Bool → Bool) (ψ : State) : State :=
  fun p => ψ (p.1, xor p.2 (f p.1))

/-- The initial state `|0⟩|1⟩`. -/
noncomputable def init : State := fun p => if p = (false, true) then 1 else 0

/-- The final state of Deutsch's algorithm: prepare `|0⟩|1⟩`, apply a Hadamard gate to
each qubit, query the oracle **exactly once**, then apply a Hadamard gate to the first
qubit. -/
noncomputable def deutsch (f : Bool → Bool) : State :=
  had₁ (oracle f (had₁ (had₂ init)))

/-- The probability that measuring the first qubit of the final state yields `0`. -/
noncomputable def probZero (f : Bool → Bool) : ℝ :=
  ‖deutsch f (false, false)‖ ^ 2 + ‖deutsch f (false, true)‖ ^ 2

/-- The probability that measuring the first qubit of the final state yields `1`. -/
noncomputable def probOne (f : Bool → Bool) : ℝ :=
  ‖deutsch f (true, false)‖ ^ 2 + ‖deutsch f (true, true)‖ ^ 2

/-- Closed form for the amplitudes of the final state on the basis vectors whose first
qubit is `0`: they are proportional to `(-1)^{f 0} + (-1)^{f 1}`. -/
theorem deutsch_amp (f : Bool → Bool) (y : Bool) :
    deutsch f (false, y) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 3 * sgn y * (sgn (f false) + sgn (f true)) := by
  cases y <;> cases hf : f false <;> cases ht : f true <;>
    simp [deutsch, had₁, had₂, oracle, init, sgn, hf, ht, Prod.ext_iff] <;> ring

/-- If `f` is constant, the algorithm measures `0` on the first qubit with certainty. -/
theorem probZero_of_const (f : Bool → Bool) (h : f false = f true) : probZero f = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    have h63 : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    rw [h63, hs]; norm_num
  simp only [probZero, deutsch_amp, h]
  cases ht : f true <;>
    simp [sgn, Complex.norm_real, mul_pow, abs_of_nonneg, Real.sqrt_nonneg] <;>
    field_simp <;> norm_num [h6]

/-- If `f` is balanced, the algorithm never measures `0` on the first qubit. -/
theorem probZero_of_balanced (f : Bool → Bool) (h : f false ≠ f true) : probZero f = 0 := by
  simp only [probZero, deutsch_amp]
  cases hf : f false <;> cases ht : f true <;> simp_all [sgn]

/-- Closed form for the amplitudes of the final state on the basis vectors whose first
qubit is `1`: they are proportional to `(-1)^{f 0} - (-1)^{f 1}`. -/
theorem deutsch_amp_one (f : Bool → Bool) (y : Bool) :
    deutsch f (true, y) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 3 * sgn y * (sgn (f false) - sgn (f true)) := by
  cases y <;> cases hf : f false <;> cases ht : f true <;>
    simp [deutsch, had₁, had₂, oracle, init, sgn, hf, ht, Prod.ext_iff] <;> ring

/-- If `f` is constant, the algorithm never measures `1` on the first qubit. -/
theorem probOne_of_const (f : Bool → Bool) (h : f false = f true) : probOne f = 0 := by
  simp only [probOne, deutsch_amp_one, h]
  cases ht : f true <;> simp [sgn]

/-- If `f` is balanced, the algorithm measures `1` on the first qubit with certainty. -/
theorem probOne_of_balanced (f : Bool → Bool) (h : f false ≠ f true) : probOne f = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    have h63 : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    rw [h63, hs]; norm_num
  simp only [probOne, deutsch_amp_one]
  cases hf : f false <;> cases ht : f true <;> rw [hf, ht] at h <;>
    simp_all [sgn, Complex.norm_real, mul_pow, abs_of_nonneg, Real.sqrt_nonneg] <;>
    field_simp <;> norm_num [h6]

/-- The measurement outcomes are exhaustive: the final state is a unit vector, so the two
probabilities sum to one. -/
theorem probZero_add_probOne (f : Bool → Bool) : probZero f + probOne f = 1 := by
  by_cases h : f false = f true
  · rw [probZero_of_const f h, probOne_of_const f h]; norm_num
  · rw [probZero_of_balanced f h, probOne_of_balanced f h]; norm_num

/-- **Deutsch's algorithm is correct.** Using a single query to the oracle `U_f`, the
measurement of the first qubit of the final state distinguishes constant from balanced
functions with certainty: the outcome is `0` with probability `1` exactly when `f` is
constant, and it is `1` with probability `1` (equivalently, `0` occurs with probability
`0`) exactly when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    (probZero f = 1 ↔ ∀ x y, f x = f y) ∧ (probOne f = 1 ↔ ∃ x y, f x ≠ f y) := by
  by_cases h : f false = f true
  · have hconst : ∀ x y, f x = f y := by
      intro x y; cases x <;> cases y <;> first | rfl | exact h | exact h.symm
    refine ⟨⟨fun _ => hconst, fun _ => probZero_of_const f h⟩,
      ⟨fun h0 => ?_, fun ⟨x, y, hxy⟩ => absurd (hconst x y) hxy⟩⟩
    rw [probOne_of_const f h] at h0; norm_num at h0
  · refine ⟨⟨fun h1 => ?_, fun hall => absurd (hall false true) h⟩,
      ⟨fun _ => ⟨false, true, h⟩, fun _ => probOne_of_balanced f h⟩⟩
    rw [probZero_of_balanced f h] at h1; norm_num at h1

end QC

