import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/
def zeros (n : ℕ) : Bits n := fun _ => false

/-- The sign character `(-1)^(x ⬝ y)` of the `n`-fold Hadamard transform. -/
noncomputable def phaseSign (x y : Bits n) : ℂ :=
  ∏ i, (if x i && y i then (-1 : ℂ) else 1)

/-- The `n`-qubit Hadamard transform `H^{⊗ n}`. -/
noncomputable def hadamard (psi : Bits n → ℂ) : Bits n → ℂ :=
  fun y => ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ * ∑ x, phaseSign x y * psi x

/-- The phase oracle of `f`, i.e. `|x⟩ ↦ (-1)^(f x) |x⟩`; this is the effect of one query
to the standard XOR oracle on a `|−⟩` ancilla. -/
noncomputable def phaseOracle (f : Bits n → Bool) (psi : Bits n → ℂ) : Bits n → ℂ :=
  fun x => (if f x then (-1 : ℂ) else 1) * psi x

/-- The initial state `|0…0⟩`. -/
noncomputable def zeroState : Bits n → ℂ := fun x => if x = zeros n then 1 else 0

/-- The final state of the Deutsch–Jozsa circuit: `H^{⊗n}`, one oracle query, `H^{⊗n}`. -/
noncomputable def djFinal (f : Bits n → Bool) : Bits n → ℂ :=
  hadamard (phaseOracle f (hadamard (zeroState : Bits n → ℂ)))

/-- `f` is constant. -/
def IsConstant (f : Bits n → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: exactly half of its inputs are mapped to `true`. -/
def IsBalanced (f : Bits n → Bool) : Prop :=
  2 * (Finset.univ.filter (fun x : Bits n => f x = true)).card = 2 ^ n

/-! ### Basic computations -/

theorem phaseSign_right_zeros (x : Bits n) : phaseSign x (zeros n) = 1 := by
  simp [phaseSign, zeros]

theorem phaseSign_left_zeros (y : Bits n) : phaseSign (zeros n) y = 1 := by
  simp [phaseSign, zeros]

/-- The normalisation constant squared. -/
theorem norm_const_sq :
    (((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹) = ((2 : ℂ) ^ n)⁻¹ := by
  have h2 : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq : ((Real.sqrt 2 ^ n : ℝ) : ℂ) * ((Real.sqrt 2 ^ n : ℝ) : ℂ) = (2 : ℂ) ^ n := by
    rw [← Complex.ofReal_mul, ← mul_pow, h2]
    norm_cast
  rw [← mul_inv, hsq]

/-- After the first Hadamard transform the state is uniform. -/
theorem hadamard_zeroState (y : Bits n) :
    hadamard (zeroState : Bits n → ℂ) y = ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ := by
  unfold hadamard zeroState
  rw [Finset.sum_eq_single (zeros n)]
  · rw [phaseSign_left_zeros]
    simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The amplitude of any basis state `y` in the final state. -/
theorem djFinal_apply (f : Bits n → Bool) (y : Bits n) :
    djFinal f y
      = ((2 : ℂ) ^ n)⁻¹ * ∑ x : Bits n, phaseSign x y * (if f x then (-1 : ℂ) else 1) := by
  have key : ∀ x : Bits n,
      phaseSign x y * phaseOracle f (hadamard (zeroState : Bits n → ℂ)) x
        = ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ * (phaseSign x y * (if f x then (-1 : ℂ) else 1)) := by
    intro x
    simp only [phaseOracle]
    rw [hadamard_zeroState]
    ring
  show ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ *
      ∑ x : Bits n, phaseSign x y *
        phaseOracle f (hadamard (zeroState : Bits n → ℂ)) x = _
  rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.mul_sum, ← mul_assoc, norm_const_sq]

/-- The amplitude of `|0…0⟩` in the final state is the normalised character sum of `f`. -/
theorem djFinal_zeros (f : Bits n → Bool) :
    djFinal f (zeros n) = ((2 : ℂ) ^ n)⁻¹ * ∑ x : Bits n, (if f x then (-1 : ℂ) else 1) := by
  rw [djFinal_apply]
  simp only [phaseSign_right_zeros, one_mul]

/-- Orthogonality of the Hadamard characters: for `y ≠ 0…0` the character sum vanishes. -/
theorem sum_phaseSign_eq_zero {y : Bits n} (hy : y ≠ zeros n) :
    ∑ x : Bits n, phaseSign x y = (0 : ℂ) := by
  have hfac : ∑ x : Bits n, phaseSign x y
      = ∏ i, ∑ b : Bool, (if b && y i then (-1 : ℂ) else 1) :=
    (Fintype.prod_sum (fun i b => if b && y i then (-1 : ℂ) else 1)).symm
  rw [hfac]
  obtain ⟨i, hi⟩ : ∃ i, y i = true := by
    by_contra h
    push_neg at h
    exact hy (funext fun i => by simpa using h i)
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [hi]

/-- The character sum of `f` in terms of the number of `true` values. -/
theorem char_sum (f : Bits n → Bool) :
    ∑ x : Bits n, (if f x then (-1 : ℂ) else 1)
      = (2 : ℂ) ^ n - 2 * ((Finset.univ.filter (fun x : Bits n => f x = true)).card : ℂ) := by
  classical
  have hsplit :
      ∑ x : Bits n, (if f x then (-1 : ℂ) else 1)
        = ∑ x ∈ Finset.univ.filter (fun x : Bits n => f x = true), (-1 : ℂ)
          + ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (f x = true)), (1 : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Bits n => f x = true)]
    congr 1
    · exact Finset.sum_congr rfl (by intro x hx; simp at hx; simp [hx])
    · exact Finset.sum_congr rfl (by intro x hx; simp at hx; simp [hx])
  rw [hsplit]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have hcard :
      (Finset.univ.filter (fun x : Bits n => f x = true)).card
        + (Finset.univ.filter (fun x : Bits n => ¬ (f x = true))).card
        = Fintype.card (Bits n) :=
    Finset.card_filter_add_card_filter_not _
  have hc : Fintype.card (Bits n) = 2 ^ n := by
    simp [Bits]
  rw [hc] at hcard
  have hcast := congrArg (fun m : ℕ => (m : ℂ)) hcard
  push_cast at hcast
  have hnot : ((Finset.univ.filter (fun x : Bits n => ¬ (f x = true))).card : ℂ)
      = (2 : ℂ) ^ n - ((Finset.univ.filter (fun x : Bits n => f x = true)).card : ℂ) := by
    linear_combination hcast
  rw [hnot]
  ring

/-! ### The theorem -/

/-- In the constant case every amplitude other than that of `|0…0⟩` vanishes. -/
theorem djFinal_eq_zero_of_isConstant {f : Bits n → Bool} (hconst : IsConstant f)
    {y : Bits n} (hy : y ≠ zeros n) : djFinal f y = 0 := by
  have hval : ∀ x : Bits n, (if f x then (-1 : ℂ) else 1)
      = (if f (zeros n) then (-1 : ℂ) else 1) := by
    intro x
    rw [hconst x (zeros n)]
  rw [djFinal_apply]
  simp only [hval]
  rw [← Finset.sum_mul, sum_phaseSign_eq_zero hy]
  ring

/--
**Deutsch–Jozsa.**  Prepare `|0…0⟩`, apply `H^{⊗n}`, make a *single* query to the phase oracle
of `f`, and apply `H^{⊗n}` again.

* If `f` is constant, the amplitude of the all-zeros outcome has modulus `1` and every other
  amplitude vanishes, so measuring the register returns `0…0` with probability `1`.
* If `f` is balanced, the amplitude of the all-zeros outcome is `0`, so the outcome `0…0`
  never occurs.

Hence one query suffices to decide constant versus balanced.
-/
theorem deutsch_jozsa (n : ℕ) (f : Bits n → Bool) :
    (IsConstant f → ‖djFinal f (zeros n)‖ = 1 ∧ ∀ y : Bits n, y ≠ zeros n → djFinal f y = 0) ∧
    (IsBalanced f → djFinal f (zeros n) = 0) := by
  classical
  have hne : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  constructor
  · intro hconst
    refine ⟨?_, fun y hy => djFinal_eq_zero_of_isConstant hconst hy⟩
    rw [djFinal_zeros, char_sum]
    by_cases hb : f (zeros n) = true
    · -- `f` is constantly `true`, so all `2 ^ n` inputs are mapped to `true`
      have hfilter : (Finset.univ.filter (fun x : Bits n => f x = true)) = Finset.univ :=
        Finset.filter_true_of_mem (fun x _ => (hconst x (zeros n)).trans hb)
      have hc : (Finset.univ : Finset (Bits n)).card = 2 ^ n := by
        simp [Bits]
      rw [hfilter, hc]
      have h2 : ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n - 2 * ((2 ^ n : ℕ) : ℂ)) = -1 := by
        push_cast
        field_simp
        ring
      rw [h2]
      simp
    · -- `f` is constantly `false`, so no input is mapped to `true`
      have hall : ∀ x : Bits n, f x = false := by
        intro x
        simp only [Bool.not_eq_true] at hb
        rw [hconst x (zeros n), hb]
      have hfilter : (Finset.univ.filter (fun x : Bits n => f x = true)) = ∅ :=
        Finset.filter_false_of_mem (fun x _ => by simp [hall x])
      rw [hfilter]
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero]
      rw [inv_mul_cancel₀ hne]
      simp
  · intro hbal
    rw [djFinal_zeros, char_sum]
    have hcast := congrArg (fun m : ℕ => (m : ℂ)) hbal
    push_cast at hcast
    rw [show ((2 : ℂ) ^ n - 2 * ((Finset.univ.filter (fun x : Bits n => f x = true)).card : ℂ))
        = 0 by linear_combination -hcast]
    simp

end QI

