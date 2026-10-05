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

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/
def sign (b : Bool) : ℂ := if b then -1 else 1

/-- The Walsh–Hadamard character `(-1)^(x ⬝ y)` on bit strings. -/
def chi (x y : Fin n → Bool) : ℂ := ∏ i, sign (x i && y i)

/-- The all-zeros bit string of length `n`. -/
def zeroStr (n : ℕ) : Fin n → Bool := fun _ => false

/-- The normalization constant `2^(-n/2)`. -/
noncomputable def hcoeff (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹

/-- The `n`-fold Hadamard transform acting on state vectors indexed by bit strings. -/
noncomputable def hadamard (ψ : (Fin n → Bool) → ℂ) : (Fin n → Bool) → ℂ :=
  fun y => hcoeff n * ∑ x : Fin n → Bool, chi x y * ψ x

/-- The phase (`f`-controlled sign) oracle: this is the *single* query to `f`. -/
def phaseOracle (f : (Fin n → Bool) → Bool) (ψ : (Fin n → Bool) → ℂ) :
    (Fin n → Bool) → ℂ := fun x => sign (f x) * ψ x

/-- The initial state `|0…0⟩`. -/
def initState (n : ℕ) : (Fin n → Bool) → ℂ := fun x => if x = zeroStr n then 1 else 0

/-- The state produced by the Deutsch–Jozsa circuit: `H^{⊗n}`, one oracle query,
then `H^{⊗n}` again. -/
noncomputable def djState (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℂ :=
  hadamard (phaseOracle f (hadamard (initState n)))

/-- Born-rule probability of observing the outcome `y`. -/
noncomputable def prob (ψ : (Fin n → Bool) → ℂ) (y : Fin n → Bool) : ℝ := ‖ψ y‖ ^ 2

/-- `f` is constant. -/
def IsConstant (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: it takes the value `true` on exactly half of its inputs. -/
def IsBalanced (f : (Fin n → Bool) → Bool) : Prop :=
  {x : Fin n → Bool | f x = true}.toFinset.card = {x : Fin n → Bool | f x = false}.toFinset.card

lemma norm_sign (b : Bool) : ‖sign b‖ = 1 := by
  cases b <;> simp [sign]

lemma chi_zeroStr_right (x : Fin n → Bool) : chi x (zeroStr n) = 1 := by
  simp [chi, zeroStr, sign]

lemma chi_zeroStr_left (y : Fin n → Bool) : chi (zeroStr n) y = 1 := by
  simp [chi, zeroStr, sign]

lemma hcoeff_sq (n : ℕ) : hcoeff n * hcoeff n = ((2 ^ n : ℝ) : ℂ)⁻¹ := by
  have h : (0 : ℝ) ≤ 2 ^ n := by positivity
  rw [hcoeff, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt h]

lemma hadamard_initState : hadamard (initState n) = fun _ => hcoeff n := by
  funext y
  simp [hadamard, initState, chi_zeroStr_left]

/-- The amplitude of the all-zeros outcome is the normalized `±1` average of `f`. -/
lemma djState_zeroStr (f : (Fin n → Bool) → Bool) :
    djState f (zeroStr n) = ((2 ^ n : ℝ) : ℂ)⁻¹ * ∑ x : Fin n → Bool, sign (f x) := by
  have h1 : ∀ x : Fin n → Bool, phaseOracle f (hadamard (initState n)) x
      = sign (f x) * hcoeff n := by
    intro x; simp [phaseOracle, hadamard_initState]
  calc djState f (zeroStr n)
      = hcoeff n * ∑ x : Fin n → Bool, chi x (zeroStr n)
          * (phaseOracle f (hadamard (initState n)) x) := rfl
    _ = hcoeff n * ∑ x : Fin n → Bool, sign (f x) * hcoeff n := by
        refine congrArg _ (Finset.sum_congr rfl ?_)
        intro x _; rw [chi_zeroStr_right, one_mul, h1]
    _ = (hcoeff n * hcoeff n) * ∑ x : Fin n → Bool, sign (f x) := by
        rw [← Finset.sum_mul]; ring
    _ = ((2 ^ n : ℝ) : ℂ)⁻¹ * ∑ x : Fin n → Bool, sign (f x) := by rw [hcoeff_sq]

lemma card_bitstrings : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  simp

lemma sum_sign_of_constant {f : (Fin n → Bool) → Bool} (hf : IsConstant f) :
    ∑ x : Fin n → Bool, sign (f x) = (2 ^ n : ℂ) * sign (f (zeroStr n)) := by
  have : ∀ x ∈ (Finset.univ : Finset (Fin n → Bool)), sign (f x) = sign (f (zeroStr n)) := by
    intro x _; rw [hf x (zeroStr n)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_bitstrings, nsmul_eq_mul]
  push_cast
  ring

lemma sum_sign_of_balanced {f : (Fin n → Bool) → Bool} (hf : IsBalanced f) :
    ∑ x : Fin n → Bool, sign (f x) = 0 := by
  classical
  set T : Finset (Fin n → Bool) := Finset.univ.filter (fun x => f x = true) with hTdef
  set F : Finset (Fin n → Bool) := Finset.univ.filter (fun x => f x = false) with hFdef
  have hFeq : F = Finset.univ.filter (fun x : Fin n → Bool => ¬ (f x = true)) := by
    rw [hFdef]; ext x; simp
  have hsplit :
      ∑ x : Fin n → Bool, sign (f x)
        = (∑ x ∈ T, sign (f x)) + ∑ x ∈ F, sign (f x) := by
    rw [hFeq, hTdef]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : (∑ x ∈ T, sign (f x)) = ∑ _x ∈ T, (-1 : ℂ) :=
    Finset.sum_congr rfl (fun x hx => by
      have : f x = true := by rw [hTdef] at hx; simpa using hx
      simp [sign, this])
  have h2 : (∑ x ∈ F, sign (f x)) = ∑ _x ∈ F, (1 : ℂ) :=
    Finset.sum_congr rfl (fun x hx => by
      have : f x = false := by rw [hFdef] at hx; simpa using hx
      simp [sign, this])
  have hcard : (T.card : ℂ) = (F.card : ℂ) := by
    have hT : {x : Fin n → Bool | f x = true}.toFinset = T := by rw [hTdef]; ext x; simp
    have hF : {x : Fin n → Bool | f x = false}.toFinset = F := by rw [hFdef]; ext x; simp
    have hf' : {x : Fin n → Bool | f x = true}.toFinset.card
        = {x : Fin n → Bool | f x = false}.toFinset.card := hf
    rw [hT, hF] at hf'
    exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hf'
  rw [hsplit, h1, h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard]
  ring

/-- **Deutsch–Jozsa.**  Running `H^{⊗n}`, a *single* query to the phase oracle for `f`,
and `H^{⊗n}` again, the all-zeros measurement outcome occurs with probability `1` when
`f` is constant and with probability `0` when `f` is balanced.  Hence one query suffices
to decide constant vs. balanced. -/
theorem deutsch_jozsa (f : (Fin n → Bool) → Bool) :
    (IsConstant f → prob (djState f) (zeroStr n) = 1) ∧
    (IsBalanced f → prob (djState f) (zeroStr n) = 0) := by
  constructor
  · intro hf
    have h : djState f (zeroStr n) = sign (f (zeroStr n)) := by
      rw [djState_zeroStr, sum_sign_of_constant hf]
      have h2 : ((2 ^ n : ℝ) : ℂ) ≠ 0 := by
        simp
      push_cast at h2 ⊢
      field_simp
    rw [prob, h, norm_sign, one_pow]
  · intro hf
    have h : djState f (zeroStr n) = 0 := by
      rw [djState_zeroStr, sum_sign_of_balanced hf, mul_zero]
    rw [prob, h, norm_zero]
    norm_num

end QI

