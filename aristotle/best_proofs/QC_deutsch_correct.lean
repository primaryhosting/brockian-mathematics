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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Deutsch's algorithm

We model a two-qubit quantum register by its amplitude vector
`Bool × Bool → ℂ` (the computational basis is indexed by pairs of bits),
implement the Hadamard gates on each qubit and the phase-kickback oracle
`U_f |x,y⟩ = |x, y ⊕ f x⟩` as linear maps on this space, and prove that
Deutsch's algorithm — which queries the oracle exactly once — decides
whether `f : {0,1} → {0,1}` is constant or balanced with certainty.
-/

namespace QC

noncomputable section

/-- The state space of two qubits: amplitudes indexed by the computational basis. -/
abbrev State : Type := Bool × Bool → ℂ

/-- The sign `(-1)^b` of a bit. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

@[simp] lemma sgn_false : sgn false = 1 := rfl
@[simp] lemma sgn_true : sgn true = -1 := rfl

/-- The Hadamard gate applied to the first qubit. -/
def H1 (s : State) : State :=
  fun p => (Real.sqrt 2 : ℂ)⁻¹ * (s (false, p.2) + sgn p.1 * s (true, p.2))

/-- The Hadamard gate applied to the second qubit. -/
def H2 (s : State) : State :=
  fun p => (Real.sqrt 2 : ℂ)⁻¹ * (s (p.1, false) + sgn p.2 * s (p.1, true))

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`, acting on amplitude vectors. -/
def oracle (f : Bool → Bool) (s : State) : State :=
  fun p => s (p.1, xor p.2 (f p.1))

/-- The initial state `|0⟩|1⟩`. -/
def init : State := fun p => if p = (false, true) then 1 else 0

/-- The state produced by Deutsch's algorithm: prepare `|0⟩|1⟩`, apply a
Hadamard gate to each qubit, query the oracle **once**, then apply a Hadamard
gate to the first qubit. -/
def deutschState (f : Bool → Bool) : State := H1 (oracle f (H1 (H2 init)))

/-- Probability of measuring `0` on the first qubit of the final state. -/
def probZero (f : Bool → Bool) : ℝ := ∑ y : Bool, ‖deutschState f (false, y)‖ ^ 2

/-- Probability of measuring `1` on the first qubit of the final state. -/
def probOne (f : Bool → Bool) : ℝ := ∑ y : Bool, ‖deutschState f (true, y)‖ ^ 2

/-- Closed form for the final amplitudes. -/
lemma deutschState_apply (f : Bool → Bool) (b y : Bool) :
    deutschState f (b, y)
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ 3 * sgn y * (sgn (f false) + sgn b * sgn (f true)) := by
  simp only [deutschState, H1, H2, oracle, init]
  cases b <;>
    cases hy : y <;>
      cases h0 : f false <;>
        cases h1 : f true <;>
          simp [sgn] <;> ring

lemma sqrt_two_cube_sq : (Real.sqrt 2 ^ 3) ^ 2 = 8 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (Real.sqrt 2 ^ 3) ^ 2 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    _ = 8 := by rw [hsq]; norm_num

/-- The measurement probabilities of Deutsch's algorithm. -/
theorem probZero_eq (f : Bool → Bool) :
    probZero f = if f false = f true then 1 else 0 := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [probZero, deutschState_apply, Fintype.sum_bool]
  cases h0 : f false <;> cases h1 : f true <;>
    simp [norm_pow, mul_pow, inv_pow, sgn, abs_of_pos hs] <;>
    rw [sqrt_two_cube_sq] <;> norm_num

/-- The measurement probabilities of Deutsch's algorithm. -/
theorem probOne_eq (f : Bool → Bool) :
    probOne f = if f false = f true then 0 else 1 := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [probOne, deutschState_apply, Fintype.sum_bool]
  cases h0 : f false <;> cases h1 : f true <;>
    simp [norm_pow, mul_pow, inv_pow, sgn, abs_of_pos hs] <;>
    rw [sqrt_two_cube_sq] <;> norm_num

/-- **Deutsch's algorithm.**  Using a single query to the oracle `U_f`, the
measurement of the first qubit of `deutschState f` returns `0` with
probability `1` when `f` is constant, and returns `1` with probability `1`
when `f` is balanced.  In particular the outcome decides constant vs.
balanced with certainty. -/
theorem deutsch_correct (f : Bool → Bool) :
    (f false = f true → probZero f = 1 ∧ probOne f = 0) ∧
    (f false ≠ f true → probZero f = 0 ∧ probOne f = 1) := by
  constructor
  · intro h
    simp [probZero_eq, probOne_eq, h]
  · intro h
    simp [probZero_eq, probOne_eq, h]

/-- Sanity check: the two measurement outcomes have total probability one. -/
theorem probZero_add_probOne (f : Bool → Bool) : probZero f + probOne f = 1 := by
  rcases eq_or_ne (f false) (f true) with h | h
  · obtain ⟨h1, h2⟩ := (deutsch_correct f).1 h
    rw [h1, h2]; norm_num
  · obtain ⟨h1, h2⟩ := (deutsch_correct f).2 h
    rw [h1, h2]; norm_num

#print axioms QC.deutsch_correct

end

end QC

