/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-!
## The Deutsch–Jozsa circuit

We model the `n`-qubit register by its (real) amplitude vector, a function
`(Fin n → Bool) → ℝ`, indexed by bit strings.  The circuit is

`|0…0⟩  --H^{⊗n}-->  --U_f (phase kickback)-->  --H^{⊗n}-->  measure`.

Everything below is stated for real amplitudes, which suffices because all gates
involved (Hadamard and the phase oracle) have real matrix entries.
-/

/-- The all-zeros bit string. -/
def zeroStr (n : ℕ) : Fin n → Bool := fun _ => false

/-- The `±1` phase attached to a Boolean value: `false ↦ 1`, `true ↦ -1`.
This is `(-1)^b`. -/
def phase (b : Bool) : ℝ := if b then -1 else 1

/-- The sign `(-1)^{x·y}` appearing in the `n`-fold Hadamard transform, where `x · y`
is the mod-2 inner product of the bit strings `x` and `y`. -/
def signIP {n : ℕ} (x y : Fin n → Bool) : ℝ := ∏ i, if x i && y i then (-1 : ℝ) else 1

/-- The computational basis state `|z⟩`. -/
def basisVec {n : ℕ} (z : Fin n → Bool) : (Fin n → Bool) → ℝ := fun x => if x = z then 1 else 0

/-- The `n`-fold Hadamard transform `H^{⊗n}`, acting on amplitude vectors:
`(Hψ)(y) = 2^{-n/2} ∑ₓ (-1)^{x·y} ψ(x)`. -/
noncomputable def hadamard {n : ℕ} (psi : (Fin n → Bool) → ℝ) : (Fin n → Bool) → ℝ :=
  fun y => ((Real.sqrt 2) ^ n)⁻¹ * ∑ x : Fin n → Bool, signIP x y * psi x

/-- The phase oracle obtained from a single query to `f` (phase kickback):
`ψ(x) ↦ (-1)^{f x} ψ(x)`. -/
def phaseOracle {n : ℕ} (f : (Fin n → Bool) → Bool) (psi : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ := fun x => phase (f x) * psi x

/-- The state produced by the Deutsch–Jozsa circuit: Hadamard layer, **one** oracle query,
Hadamard layer, applied to `|0…0⟩`. -/
noncomputable def djState {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ :=
  hadamard (phaseOracle f (hadamard (basisVec (zeroStr n))))

/-- The amplitude of the all-zeros outcome of the Deutsch–Jozsa circuit,
`2⁻ⁿ ∑ₓ (-1)^{f x}`. -/
noncomputable def djAmp {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, phase (f x)

/-- `f` is constant. -/
def IsConstantFn {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: exactly half of the `2ⁿ` inputs are mapped to `true`. -/
def IsBalancedFn {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  2 * (Finset.univ.filter fun x : Fin n → Bool => f x = true).card = 2 ^ n

/-!
## Basic computations
-/

lemma sqrt_two_pow_mul_self (n : ℕ) :
    ((Real.sqrt 2) ^ n) * ((Real.sqrt 2) ^ n) = (2 : ℝ) ^ n := by
  rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]

/-- The Hadamard sign is `1` whenever one of the arguments is the all-zeros string. -/
lemma signIP_zeroStr_left {n : ℕ} (x : Fin n → Bool) : signIP (zeroStr n) x = 1 := by
  simp [signIP, zeroStr]

lemma signIP_zeroStr_right {n : ℕ} (x : Fin n → Bool) : signIP x (zeroStr n) = 1 := by
  simp [signIP, zeroStr]

/-- Orthogonality of the Hadamard characters: `∑ₓ (-1)^{x·y}` is `2ⁿ` for `y = 0…0`
and `0` otherwise. -/
lemma sum_signIP {n : ℕ} (y : Fin n → Bool) :
    ∑ x : Fin n → Bool, signIP x y = if y = zeroStr n then (2 : ℝ) ^ n else 0 := by
  have hswap : ∑ x : Fin n → Bool, (∏ i, if x i && y i then (-1 : ℝ) else 1)
      = ∏ i, ∑ b : Bool, (if b && y i then (-1 : ℝ) else 1) :=
    (Finset.prod_univ_sum (fun _ => Finset.univ) fun i b => if b && y i then (-1 : ℝ) else 1).symm
  have hfac : ∀ i : Fin n, ∑ b : Bool, (if b && y i then (-1 : ℝ) else 1)
      = if y i then (0 : ℝ) else 2 := by
    intro i
    cases y i <;> simp
  simp only [signIP]
  rw [hswap, Finset.prod_congr rfl fun i _ => hfac i]
  by_cases hy : y = zeroStr n
  · subst hy
    simp [zeroStr]
  · rw [if_neg hy]
    obtain ⟨i, hi⟩ : ∃ i, y i = true := by
      by_contra hcon
      push_neg at hcon
      exact hy (funext fun i => by simpa [zeroStr] using hcon i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- After the first Hadamard layer the register is in the uniform superposition. -/
lemma hadamard_basisVec_zero {n : ℕ} :
    hadamard (basisVec (zeroStr n)) = fun _ : Fin n → Bool => ((Real.sqrt 2) ^ n)⁻¹ := by
  funext y
  rw [hadamard]
  have : ∑ x : Fin n → Bool, signIP x y * basisVec (zeroStr n) x = signIP (zeroStr n) y := by
    simp [basisVec]
  rw [this, signIP_zeroStr_left, mul_one]

/-- The state at the end of the circuit, in closed form. -/
lemma djState_apply {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) :
    djState f y = ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, signIP x y * phase (f x) := by
  rw [djState, hadamard_basisVec_zero, hadamard]
  have hstep : ∀ x : Fin n → Bool,
      signIP x y * phaseOracle f (fun _ => ((Real.sqrt 2) ^ n)⁻¹) x
        = ((Real.sqrt 2) ^ n)⁻¹ * (signIP x y * phase (f x)) := by
    intro x
    rw [phaseOracle]
    ring
  rw [Finset.sum_congr rfl fun x _ => hstep x, ← Finset.mul_sum, ← mul_assoc, ← mul_inv,
    sqrt_two_pow_mul_self]

/-- The all-zeros amplitude of the circuit output is exactly `2⁻ⁿ ∑ₓ (-1)^{f x}`. -/
theorem djState_zeroStr {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djState f (zeroStr n) = djAmp f := by
  rw [djState_apply, djAmp]
  simp [signIP_zeroStr_right]

/-!
## The amplitude in the two promise cases
-/

/-- The phase sum counts `#{f = false} - #{f = true}`. -/
lemma sum_phase {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ x : Fin n → Bool, phase (f x) =
      (2 : ℝ) ^ n - 2 * (Finset.univ.filter fun x : Fin n → Bool => f x = true).card := by
  have h : ∀ x : Fin n → Bool,
      phase (f x) = 1 - 2 * (if f x = true then (1 : ℝ) else 0) := by
    intro x
    by_cases hx : f x = true <;> norm_num [phase, hx]
  rw [Finset.sum_congr rfl fun x _ => h x]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

/-- The amplitude in terms of the number of `true` inputs. -/
lemma djAmp_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f = ((2 : ℝ) ^ n)⁻¹ *
      ((2 : ℝ) ^ n - 2 * (Finset.univ.filter fun x : Fin n → Bool => f x = true).card) := by
  rw [djAmp, sum_phase]

/-- If `f` is balanced, the all-zeros amplitude vanishes: the measurement never returns
the all-zeros string, so the algorithm correctly reports "balanced". -/
theorem djAmp_of_balanced {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsBalancedFn f) :
    djAmp f = 0 := by
  rw [djAmp_eq]
  have h' : (2 : ℝ) * (Finset.univ.filter fun x : Fin n → Bool => f x = true).card
      = (2 : ℝ) ^ n := by
    have := congrArg (fun k : ℕ => (k : ℝ)) h
    push_cast at this
    simpa using this
  rw [h']
  ring

/-- If `f` is constant, the circuit output is `±|0…0⟩`: all the amplitude sits on the
all-zeros string. -/
theorem djState_of_constant {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsConstantFn f)
    (y : Fin n → Bool) :
    djState f y = phase (f (zeroStr n)) * (if y = zeroStr n then 1 else 0) := by
  have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hconst : ∀ x : Fin n → Bool, phase (f x) = phase (f (zeroStr n)) := by
    intro x; rw [h x (zeroStr n)]
  rw [djState_apply, Finset.sum_congr rfl fun x _ => by rw [hconst x], ← Finset.sum_mul,
    sum_signIP]
  by_cases hy : y = zeroStr n
  · rw [if_pos hy, if_pos hy, ← mul_assoc, inv_mul_cancel₀ hpow]
    ring
  · rw [if_neg hy, if_neg hy]
    ring

/-- If `f` is constant, the all-zeros amplitude has modulus `1`: the measurement returns
the all-zeros string with probability one, so the algorithm correctly reports "constant". -/
theorem abs_djAmp_of_constant {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsConstantFn f) :
    |djAmp f| = 1 := by
  rw [← djState_zeroStr, djState_of_constant f h, if_pos rfl, mul_one]
  cases hb : f (zeroStr n) <;> norm_num [phase]

/-!
## Deutsch–Jozsa
-/

/-- **Deutsch–Jozsa.**  Let `f : {0,1}ⁿ → {0,1}` satisfy the promise that it is either
constant or balanced.  Running the Deutsch–Jozsa circuit — a Hadamard layer, a **single**
query to the oracle for `f`, and a second Hadamard layer, applied to `|0…0⟩` — and measuring
in the computational basis decides which case holds:

* the amplitude of the all-zeros outcome is `2⁻ⁿ ∑ₓ (-1)^{f x}`;
* it is nonzero exactly when `f` is constant, in which case its modulus (hence the
  probability of observing `0…0`) is `1`;
* it is zero exactly when `f` is balanced, i.e. `0…0` is then never observed.

So one query suffices. -/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hpromise : IsConstantFn f ∨ IsBalancedFn f) :
    djState f (zeroStr n) = djAmp f ∧
    (IsConstantFn f ↔ djState f (zeroStr n) ≠ 0) ∧
    (IsBalancedFn f ↔ djState f (zeroStr n) = 0) ∧
    (IsConstantFn f → (djState f (zeroStr n)) ^ 2 = 1) ∧
    (IsBalancedFn f → (djState f (zeroStr n)) ^ 2 = 0) := by
  have hz : djState f (zeroStr n) = djAmp f := djState_zeroStr f
  have hconst : IsConstantFn f → |djAmp f| = 1 := fun hc => abs_djAmp_of_constant f hc
  have hsq : IsConstantFn f → (djAmp f) ^ 2 = 1 := by
    intro hc
    have := hconst hc
    have : |djAmp f| ^ 2 = 1 := by rw [this]; norm_num
    simpa [sq_abs] using this
  refine ⟨hz, ⟨fun hc => ?_, fun hne => ?_⟩, ⟨fun hb => ?_, fun h0 => ?_⟩,
    fun hc => by rw [hz]; exact hsq hc, fun hb => by rw [hz, djAmp_of_balanced f hb]; ring⟩
  · rw [hz]
    intro h0
    have := hconst hc
    rw [h0] at this
    norm_num at this
  · rcases hpromise with hc | hb
    · exact hc
    · rw [hz, djAmp_of_balanced f hb] at hne
      exact absurd rfl hne
  · rw [hz, djAmp_of_balanced f hb]
  · rcases hpromise with hc | hb
    · rw [hz] at h0
      have := hconst hc
      rw [h0] at this
      norm_num at this
    · exact hb

/-!
## Worked instances

Two concrete sanity checks of the model: the identity on one bit and parity on two bits
are balanced, so the circuit never outputs `0…0`; a constant function outputs `0…0`
with certainty.
-/

/-- `f x = x₀` on one bit is balanced. -/
lemma isBalanced_id_one : IsBalancedFn (fun x : Fin 1 → Bool => x 0) := by
  simp only [IsBalancedFn]
  decide

/-- On one bit, the Deutsch–Jozsa circuit applied to `f x = x₀` never returns `0`. -/
example : djState (fun x : Fin 1 → Bool => x 0) (zeroStr 1) = 0 := by
  rw [djState_zeroStr]
  exact djAmp_of_balanced _ isBalanced_id_one

/-- Parity on two bits is balanced. -/
lemma isBalanced_xor_two : IsBalancedFn (fun x : Fin 2 → Bool => xor (x 0) (x 1)) := by
  simp only [IsBalancedFn]
  decide

/-- On two bits, the Deutsch–Jozsa circuit applied to parity never returns `00`. -/
example : djState (fun x : Fin 2 → Bool => xor (x 0) (x 1)) (zeroStr 2) = 0 := by
  rw [djState_zeroStr]
  exact djAmp_of_balanced _ isBalanced_xor_two

/-- For the constant function `true` on `n` bits, the circuit outputs `0…0` with
certainty (amplitude `-1`). -/
example (n : ℕ) : djState (fun _ : Fin n → Bool => true) (zeroStr n) = -1 := by
  have h : IsConstantFn (fun _ : Fin n → Bool => true) := fun _ _ => rfl
  rw [djState_of_constant _ h, if_pos rfl]
  norm_num [phase]

end QI

