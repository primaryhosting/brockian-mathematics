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

/-! ## The two-qubit state space

A two-qubit state is described by its amplitude function `Bool × Bool → ℂ`,
where `(x, y)` denotes the computational basis state `|x⟩ ⊗ |y⟩`
(with `false = 0` and `true = 1`). -/

/-- The sign `(-1)^b`. -/
noncomputable def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- The normalisation constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- The initial state `|0⟩ ⊗ |1⟩`. -/
noncomputable def init : Bool × Bool → ℂ := fun p => if p = (false, true) then 1 else 0

/-- The Hadamard gate applied to both qubits:
`H ⊗ H`, i.e. `(H⊗H)|a,b⟩ = ½ Σ_{x,y} (-1)^{a·x + b·y} |x,y⟩`. -/
noncomputable def hadamardBoth (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => invSqrt2 * invSqrt2 *
    ∑ a : Bool, ∑ b : Bool, sgn (p.1 && a) * sgn (p.2 && b) * psi (a, b)

/-- The Hadamard gate applied to the first qubit only (`H ⊗ I`). -/
noncomputable def hadamardFirst (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => invSqrt2 * ∑ a : Bool, sgn (p.1 && a) * psi (a, p.2)

/-- The oracle `U_f : |x,y⟩ ↦ |x, y ⊕ f x⟩`, acting on amplitudes. -/
noncomputable def oracle (f : Bool → Bool) (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The final state of Deutsch's algorithm: starting from `|0⟩|1⟩`, apply `H ⊗ H`,
then **one** query to the oracle `U_f`, then `H` on the first qubit. -/
noncomputable def deutschFinal (f : Bool → Bool) : Bool × Bool → ℂ :=
  hadamardFirst (oracle f (hadamardBoth init))

/-- The probability that measuring the first qubit of the final state yields `x`. -/
noncomputable def probFirst (f : Bool → Bool) (x : Bool) : ℝ :=
  ∑ y : Bool, ‖deutschFinal f (x, y)‖ ^ 2

/-- `f` is constant. -/
def IsConstant (f : Bool → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced, i.e. takes each value exactly once. -/
def IsBalanced (f : Bool → Bool) : Prop := f false ≠ f true

lemma invSqrt2_sq : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹ := by
  have h : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, h]; norm_num
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro hc
    rw [hc] at this
    norm_num at this
  simp only [invSqrt2, Complex.ofReal_inv]
  field_simp [this]

lemma norm_invSqrt2_sq : ‖invSqrt2‖ ^ 2 = (1 : ℝ) / 2 := by
  have h : ‖invSqrt2‖ = (Real.sqrt 2)⁻¹ := by
    simp [invSqrt2, Complex.norm_real, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt 2)⁻¹)]
  rw [h]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Explicit form of the final state. -/
lemma deutschFinal_eq (f : Bool → Bool) (x y : Bool) :
    deutschFinal f (x, y) =
      invSqrt2 * (2:ℂ)⁻¹ * sgn y * (sgn (f false) + sgn x * sgn (f true)) := by
  simp only [deutschFinal, hadamardFirst, oracle, hadamardBoth, init, Fintype.sum_bool]
  cases x <;> cases y <;> cases hf : f false <;> cases ht : f true <;>
    simp [sgn, hf, ht, invSqrt2_sq] <;> ring

/-- **Deutsch's algorithm is correct.**  After a single query to the oracle `U_f`,
measuring the first qubit yields `0` with probability one when `f` is constant,
and `1` with probability one when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    (IsConstant f → probFirst f false = 1 ∧ probFirst f true = 0) ∧
    (IsBalanced f → probFirst f false = 0 ∧ probFirst f true = 1) := by
  constructor
  · intro hc
    have h : f true = f false := hc true false
    constructor <;>
    · simp only [probFirst, Fintype.sum_bool, deutschFinal_eq, h]
      cases hf : f false <;>
        simp [sgn, norm_mul, mul_pow, norm_invSqrt2_sq] <;> ring
  · intro hb
    constructor <;>
    · simp only [probFirst, Fintype.sum_bool, deutschFinal_eq]
      cases hf : f false <;> cases ht : f true <;>
        simp_all [sgn, norm_mul, mul_pow, norm_invSqrt2_sq] <;> ring

end QC

