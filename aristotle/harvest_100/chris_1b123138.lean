/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/
def dotB {n : ℕ} (a b : Bits n) : ZMod 2 := ∑ k, a k * b k

/-- `(-1)^s` for `s : ZMod 2`. -/
noncomputable def sgnC (s : ZMod 2) : ℂ := if s = 0 then 1 else -1

/-- `i^t` for `t : ZMod 4`. -/
noncomputable def iPowC (t : ZMod 4) : ℂ := Complex.I ^ t.val

/-- The doubling map `ZMod 2 → ZMod 4`. -/
def dbl (s : ZMod 2) : ZMod 4 := if s = 0 then 0 else 2

/-- The `i`-th standard basis bit string. -/
def unitVec {n : ℕ} (i : Fin n) : Bits n := Pi.single i 1

/-! ## The Pauli group -/

/-- An element of the `n`-qubit Pauli group, written as `i^ph * X^xs * Z^zs`. -/
structure Pauli (n : ℕ) where
  /-- The power of `i` multiplying the Pauli monomial. -/
  ph : ZMod 4
  /-- The `X`-part exponents. -/
  xs : Bits n
  /-- The `Z`-part exponents. -/
  zs : Bits n
deriving DecidableEq

/-- The `2^n × 2^n` complex matrix of a Pauli group element:
`i^ph X^xs Z^zs |x⟩ = i^ph (-1)^(zs ⬝ x) |x + xs⟩`. -/
noncomputable def Pauli.toMat {n : ℕ} (P : Pauli n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun y x => if y = x + P.xs then iPowC P.ph * sgnC (dotB P.zs x) else 0

/-- Multiplication in the Pauli group. -/
def Pauli.mul {n : ℕ} (P Q : Pauli n) : Pauli n :=
  ⟨P.ph + Q.ph + dbl (dotB P.zs Q.xs), P.xs + Q.xs, P.zs + Q.zs⟩

/-- The Pauli `X` operator on qubit `i`. -/
def Xp {n : ℕ} (i : Fin n) : Pauli n := ⟨0, unitVec i, 0⟩

/-- The Pauli `Z` operator on qubit `i`. -/
def Zp {n : ℕ} (i : Fin n) : Pauli n := ⟨0, 0, unitVec i⟩

/-! ## Clifford gates -/

/-- The generators of the Clifford group used to build stabilizer circuits. -/
inductive Gate (n : ℕ) where
  /-- Hadamard on qubit `i`. -/
  | H (i : Fin n) : Gate n
  /-- Phase gate `diag (1, i)` on qubit `i`. -/
  | S (i : Fin n) : Gate n
  /-- CNOT with control `i` and target `j`. -/
  | CX (i j : Fin n) (h : i ≠ j) : Gate n

/-- The action of a CNOT on computational basis labels. -/
def cxMap {n : ℕ} (i j : Fin n) (x : Bits n) : Bits n := Function.update x j (x j + x i)

/-- The unitary matrix of a gate. -/
noncomputable def gateMat {n : ℕ} : Gate n → Matrix (Bits n) (Bits n) ℂ
  | .H i => ((Real.sqrt 2)⁻¹ : ℂ) • ((Xp i).toMat + (Zp i).toMat)
  | .S i => ((1 + Complex.I) / 2) • (1 : Matrix (Bits n) (Bits n) ℂ) +
      ((1 - Complex.I) / 2) • (Zp i).toMat
  | .CX i j _ => Matrix.of fun y x => if y = cxMap i j x then 1 else 0

/-- The Heisenberg (tableau) update of a Pauli operator `P ↦ g† P g`. -/
def stepPauli {n : ℕ} : Gate n → Pauli n → Pauli n
  | .H i, P => ⟨P.ph + dbl (P.xs i * P.zs i),
      Function.update P.xs i (P.zs i), Function.update P.zs i (P.xs i)⟩
  | .S i, P => ⟨P.ph + (if P.xs i = 0 then 0 else 3),
      P.xs, Function.update P.zs i (P.zs i + P.xs i)⟩
  | .CX i j _, P => ⟨P.ph,
      Function.update P.xs j (P.xs j + P.xs i), Function.update P.zs i (P.zs i + P.zs j)⟩

/-- The unitary of a stabilizer circuit, given as a list of gates in time order. -/
noncomputable def circuitMat {n : ℕ} : List (Gate n) → Matrix (Bits n) (Bits n) ℂ
  | [] => 1
  | g :: gs => circuitMat gs * gateMat g

/-- The classical tableau simulation of a circuit acting on a Pauli operator:
`P ↦ C† P C`. -/
def simulate {n : ℕ} : List (Gate n) → Pauli n → Pauli n
  | [], P => P
  | g :: gs, P => stepPauli g (simulate gs P)

/-- Reading off `⟨0…0| Q |0…0⟩` for a Pauli group element `Q`. -/
noncomputable def readout {n : ℕ} (Q : Pauli n) : ℂ := if Q.xs = 0 then iPowC Q.ph else 0

/-- The instrumented simulator: it returns the simulated Pauli together with the number of
elementary register updates performed. -/
def runInstr {n : ℕ} : List (Gate n) → Pauli n → Pauli n × ℕ
  | [], P => (P, 0)
  | g :: gs, P => let r := runInstr gs P; (stepPauli g r.1, r.2 + 3)

/-! ## Basic arithmetic lemmas -/

lemma zmod2_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by revert s; decide

lemma sgnC_add (s t : ZMod 2) : sgnC (s + t) = sgnC s * sgnC t := by
  rcases zmod2_cases s with h | h <;> rcases zmod2_cases t with h' | h' <;> subst h <;> subst h' <;>
    simp [sgnC, show (1 + 1 : ZMod 2) = 0 from by decide]

lemma iPowC_add (s t : ZMod 4) : iPowC (s + t) = iPowC s * iPowC t := by
  unfold iPowC
  rw [ZMod.val_add, ← pow_add]
  generalize (s.val + t.val) = m
  conv_rhs => rw [← Nat.div_add_mod m 4]
  rw [pow_add, pow_mul]
  simp [Complex.I_pow_four]

lemma iPowC_dbl (s : ZMod 2) : iPowC (dbl s) = sgnC s := by
  rcases zmod2_cases s with h | h <;> subst h <;>
    simp [iPowC, dbl, sgnC, show ZMod.val (2 : ZMod 4) = 2 from rfl, Complex.I_sq]

lemma dotB_add_left {n : ℕ} (a b c : Bits n) : dotB (a + b) c = dotB a c + dotB b c := by
  simp [dotB, add_mul, Finset.sum_add_distrib]

lemma dotB_add_right {n : ℕ} (a b c : Bits n) : dotB a (b + c) = dotB a b + dotB a c := by
  simp [dotB, mul_add, Finset.sum_add_distrib]

lemma dotB_zero_left {n : ℕ} (a : Bits n) : dotB 0 a = 0 := by simp [dotB]

lemma dotB_zero_right {n : ℕ} (a : Bits n) : dotB a 0 = 0 := by simp [dotB]

lemma dotB_unit_left {n : ℕ} (i : Fin n) (a : Bits n) : dotB (unitVec i) a = a i := by
  simp [dotB, unitVec, Pi.single_apply]

lemma dotB_unit_right {n : ℕ} (i : Fin n) (a : Bits n) : dotB a (unitVec i) = a i := by
  simp [dotB, unitVec, Pi.single_apply]

lemma dotB_comm {n : ℕ} (a b : Bits n) : dotB a b = dotB b a := by
  simp [dotB, mul_comm]

lemma sgnC_mul_self (s : ZMod 2) : sgnC s * sgnC s = 1 := by
  rcases zmod2_cases s with h | h <;> subst h <;> simp [sgnC]

lemma bits_add_self_cancel {n : ℕ} (x a : Bits n) : x + a + a = x := by
  ext k
  have h : a k + a k = 0 := by rcases zmod2_cases (a k) with h | h <;> simp [h]; decide
  simp [add_assoc, h]

lemma iPowC_zero : iPowC 0 = 1 := by simp [iPowC]

lemma iPowC_one : iPowC 1 = Complex.I := by
  simp [iPowC, show ZMod.val (1 : ZMod 4) = 1 from rfl]

lemma iPowC_two : iPowC 2 = -1 := by
  simp [iPowC, show ZMod.val (2 : ZMod 4) = 2 from rfl, Complex.I_sq]

lemma iPowC_three : iPowC 3 = -Complex.I := by
  simp [iPowC, show ZMod.val (3 : ZMod 4) = 3 from rfl, show (3 : ℕ) = 2 + 1 from rfl,
    pow_succ]

lemma iPowC_conj (t : ZMod 4) : star (iPowC t) = iPowC (-t) := by
  have h4 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by revert t; decide
  rcases h4 with h | h | h | h <;> subst h <;>
    simp [iPowC_zero, iPowC_one, iPowC_two, iPowC_three,
      show -(0 : ZMod 4) = 0 from by decide, show -(1 : ZMod 4) = 3 from by decide,
      show -(2 : ZMod 4) = 2 from by decide, show -(3 : ZMod 4) = 1 from by decide]

lemma sgnC_conj (s : ZMod 2) : star (sgnC s) = sgnC s := by
  rcases zmod2_cases s with h | h <;> subst h <;> simp [sgnC]

/-! ## Pauli algebra -/

lemma Pauli.toMat_mul {n : ℕ} (P Q : Pauli n) : P.toMat * Q.toMat = (P.mul Q).toMat := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (x + Q.xs)]
  · simp only [Pauli.toMat, Pauli.mul, Matrix.of_apply]
    by_cases h : y = x + (P.xs + Q.xs)
    · have h2 : y = x + Q.xs + P.xs := by rw [h]; abel
      simp only [if_pos h, if_pos h2, if_true, dotB_add_right, dotB_add_left, sgnC_add,
        iPowC_add, iPowC_dbl]
      ring
    · have h2 : ¬ (y = x + Q.xs + P.xs) := fun hh => h (by rw [hh]; abel)
      rw [if_neg h, if_neg h2, zero_mul]
  · intro z _ hz
    simp only [Pauli.toMat, Matrix.of_apply]
    rw [if_neg hz, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Pauli.toMat_one {n : ℕ} : (Pauli.mk 0 (0 : Bits n) 0).toMat = 1 := by
  ext y x
  simp [Pauli.toMat, Matrix.one_apply, iPowC_zero, dotB_zero_left, sgnC]

lemma Pauli.toMat_phase {n : ℕ} (t s : ZMod 4) (a b : Bits n) :
    (Pauli.mk (t + s) a b).toMat = iPowC s • (Pauli.mk t a b).toMat := by
  ext y x
  by_cases h : y = x + a <;> (simp [Pauli.toMat, h, iPowC_add]; try ring)

lemma Pauli.toMat_conjTranspose {n : ℕ} (P : Pauli n) :
    P.toMatᴴ = (Pauli.mk (-P.ph + dbl (dotB P.xs P.zs)) P.xs P.zs).toMat := by
  ext y x
  simp only [Matrix.conjTranspose_apply, Pauli.toMat, Matrix.of_apply]
  by_cases h : y = x + P.xs
  · have h2 : x = y + P.xs := by rw [h, bits_add_self_cancel]
    rw [if_pos h, if_pos h2, star_mul', iPowC_conj, sgnC_conj, iPowC_add, iPowC_dbl, h,
      dotB_add_right, sgnC_add, dotB_comm P.zs P.xs]
    ring
  · have h2 : ¬ (x = y + P.xs) := fun hh => h (by rw [hh, bits_add_self_cancel])
    rw [if_neg h, if_neg h2, star_zero]

/-! ## Auxiliary bit-string lemmas -/

lemma unitVec_add_self {n : ℕ} (i : Fin n) : unitVec i + unitVec i = (0 : Bits n) := by
  have h := bits_add_self_cancel (0 : Bits n) (unitVec i); simpa using h

lemma unitVec_self {n : ℕ} (i : Fin n) : (unitVec i) i = 1 := by simp [unitVec]

lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := by decide

lemma zmod2_cancel (a b : ZMod 2) : a + b + b = a := by revert a b; decide

lemma dbl_zero : dbl 0 = 0 := by simp [dbl]

lemma dbl_one : dbl 1 = 2 := by simp [dbl]

lemma update_same' {n : ℕ} (a : Bits n) (i : Fin n) (v : ZMod 2) (h : v = a i) :
    Function.update a i v = a := by subst h; exact Function.update_eq_self i a

lemma update_flip {n : ℕ} (a : Bits n) (i : Fin n) (v : ZMod 2) (h : v = a i + 1) :
    Function.update a i v = a + unitVec i := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [unitVec, h]
  · simp [Function.update_of_ne hk, unitVec, Pi.single_eq_of_ne hk]

lemma dotB_update_right {n : ℕ} (b x : Bits n) (i : Fin n) (v : ZMod 2) :
    dotB b (Function.update x i v) = dotB b x + b i * (v + x i) := by
  have key : ∀ k : Fin n, b k * (Function.update x i v) k
      = b k * x k + (if k = i then b i * (v + x i) else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, if_true, mul_add]
      linear_combination (-(b k * x k)) * zmod2_two_eq_zero
    · simp [hk]
  simp only [dotB, key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
  simp

lemma dotB_update_left {n : ℕ} (b x : Bits n) (i : Fin n) (v : ZMod 2) :
    dotB (Function.update b i v) x = dotB b x + (v + b i) * x i := by
  rw [dotB_comm, dotB_update_right, dotB_comm b x]; ring

/-! ## Products with the single-qubit Paulis -/

lemma Xp_mul {n : ℕ} (i : Fin n) (P : Pauli n) :
    (Xp i).mul P = ⟨P.ph, unitVec i + P.xs, P.zs⟩ := by
  simp [Pauli.mul, Xp, dotB_zero_left, dbl]

lemma mul_Xp {n : ℕ} (i : Fin n) (P : Pauli n) :
    P.mul (Xp i) = ⟨P.ph + dbl (P.zs i), P.xs + unitVec i, P.zs⟩ := by
  simp [Pauli.mul, Xp, dotB_unit_right]

lemma Zp_mul {n : ℕ} (i : Fin n) (P : Pauli n) :
    (Zp i).mul P = ⟨P.ph + dbl (P.xs i), P.xs, unitVec i + P.zs⟩ := by
  simp [Pauli.mul, Zp, dotB_unit_left]

lemma mul_Zp {n : ℕ} (i : Fin n) (P : Pauli n) :
    P.mul (Zp i) = ⟨P.ph, P.xs, P.zs + unitVec i⟩ := by
  simp [Pauli.mul, Zp, dotB_zero_right, dbl]

lemma Xp_conjTranspose {n : ℕ} (i : Fin n) : (Xp i).toMatᴴ = (Xp i).toMat := by
  rw [Pauli.toMat_conjTranspose]; simp [Xp, dotB_zero_right, dbl]

lemma Zp_conjTranspose {n : ℕ} (i : Fin n) : (Zp i).toMatᴴ = (Zp i).toMat := by
  rw [Pauli.toMat_conjTranspose]; simp [Zp, dotB_zero_left, dbl]

/-! ## Gate lemmas -/

lemma star_alpha : star ((1 + Complex.I) / 2 : ℂ) = (1 - Complex.I) / 2 := by simp; ring

lemma star_beta : star ((1 - Complex.I) / 2 : ℂ) = (1 + Complex.I) / 2 := by simp

lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  rw [← mul_inv, h2]
  norm_num

/-- The Hadamard gate is self-adjoint. -/
lemma H_selfadj {n : ℕ} (i : Fin n) : (gateMat (Gate.H i))ᴴ = gateMat (Gate.H i) := by
  simp only [gateMat, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Xp_conjTranspose,
    Zp_conjTranspose]
  norm_num

/-- The Hadamard gate squares to the identity. -/
lemma H_mul_H {n : ℕ} (i : Fin n) : gateMat (Gate.H i) * gateMat (Gate.H i) = 1 := by
  have hXX : (Xp i).mul (Xp i) = (⟨0, 0, 0⟩ : Pauli n) := by
    rw [mul_Xp]; simp [Xp, unitVec_add_self, dbl]
  have hZZ : (Zp i).mul (Zp i) = (⟨0, 0, 0⟩ : Pauli n) := by
    rw [mul_Zp]; simp [Zp, unitVec_add_self]
  have hXZ : (Xp i).mul (Zp i) = (⟨0, unitVec i, unitVec i⟩ : Pauli n) := by
    simp [mul_Zp, Xp]
  have hZX : (Zp i).mul (Xp i) = (⟨0 + 2, unitVec i, unitVec i⟩ : Pauli n) := by
    simp [mul_Xp, Zp, unitVec_self, dbl]
  simp only [gateMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Pauli.toMat_mul, hXX, hZZ, hXZ, hZX, Pauli.toMat_one]
  rw [Pauli.toMat_phase 0 2, iPowC_two, smul_add, smul_smul, smul_smul, sqrt_two_inv_sq]
  module

/-- Heisenberg update for the Hadamard gate, in commuted form. -/
lemma H_comm {n : ℕ} (i : Fin n) (P : Pauli n) :
    P.toMat * gateMat (Gate.H i) = gateMat (Gate.H i) * (stepPauli (Gate.H i) P).toMat := by
  simp only [gateMat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Pauli.toMat_mul, Xp_mul, mul_Xp, Zp_mul, mul_Zp]
  congr 1
  rcases zmod2_cases (P.xs i) with ha | ha <;> rcases zmod2_cases (P.zs i) with hb | hb <;>
    simp only [stepPauli]
  · have e1 : Function.update P.xs i (P.zs i) = P.xs := update_same' _ _ _ (by rw [ha, hb])
    have e2 : Function.update P.zs i (P.xs i) = P.zs := update_same' _ _ _ (by rw [ha, hb])
    rw [e1, e2, ha, hb]
    simp only [dbl_zero, add_zero, mul_zero, add_comm (unitVec i)]
  · have e1 : Function.update P.xs i (P.zs i) = P.xs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    have e2 : Function.update P.zs i (P.xs i) = P.zs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    rw [e1, e2, ha, hb]
    simp only [dbl_zero, dbl_one, zero_mul, add_zero, Pi.add_apply, unitVec_self, ha,
      bits_add_self_cancel, add_comm (unitVec i), zero_add]
    abel
  · have e1 : Function.update P.xs i (P.zs i) = P.xs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    have e2 : Function.update P.zs i (P.xs i) = P.zs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    rw [e1, e2, ha, hb]
    simp only [dbl_zero, mul_zero, add_zero, Pi.add_apply, unitVec_self, ha,
      bits_add_self_cancel, show (1 + 1 : ZMod 2) = 0 from by decide, add_comm (unitVec i)]
    abel
  · have e1 : Function.update P.xs i (P.zs i) = P.xs := update_same' _ _ _ (by rw [ha, hb])
    have e2 : Function.update P.zs i (P.xs i) = P.zs := update_same' _ _ _ (by rw [ha, hb])
    rw [e1, e2, ha, hb]
    simp only [dbl_one, one_mul, add_assoc, show (2 : ZMod 4) + 2 = 0 from by decide, add_zero,
      add_comm (unitVec i)]

/-- The phase gate is unitary. -/
lemma S_unitary {n : ℕ} (i : Fin n) : (gateMat (Gate.S i))ᴴ * gateMat (Gate.S i) = 1 := by
  have hZZ : (Zp i).mul (Zp i) = (⟨0, 0, 0⟩ : Pauli n) := by
    rw [mul_Zp]; simp [Zp, unitVec_add_self]
  simp only [gateMat, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Zp_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Pauli.toMat_mul, hZZ, Pauli.toMat_one, star_alpha, star_beta]
  match_scalars
  · linear_combination (-1/2 : ℂ) * Complex.I_sq
  · linear_combination (1/2 : ℂ) * Complex.I_sq

lemma S_unitary' {n : ℕ} (i : Fin n) : gateMat (Gate.S i) * (gateMat (Gate.S i))ᴴ = 1 := by
  have hZZ : (Zp i).mul (Zp i) = (⟨0, 0, 0⟩ : Pauli n) := by
    rw [mul_Zp]; simp [Zp, unitVec_add_self]
  simp only [gateMat, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Zp_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Pauli.toMat_mul, hZZ, Pauli.toMat_one, star_alpha, star_beta]
  match_scalars
  · linear_combination (-1/2 : ℂ) * Complex.I_sq
  · linear_combination (1/2 : ℂ) * Complex.I_sq

/-- Heisenberg update for the phase gate, in commuted form. -/
lemma S_comm {n : ℕ} (i : Fin n) (P : Pauli n) :
    P.toMat * gateMat (Gate.S i) = gateMat (Gate.S i) * (stepPauli (Gate.S i) P).toMat := by
  simp only [gateMat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Pauli.toMat_mul, Zp_mul, mul_Zp, stepPauli]
  rcases zmod2_cases (P.xs i) with ha | ha
  · have e2 : Function.update P.zs i (P.zs i + P.xs i) = P.zs :=
      update_same' _ _ _ (by rw [ha, add_zero])
    rw [e2, ha]
    simp only [if_true, add_zero, dbl_zero, add_comm (unitVec i)]
  · have e2 : Function.update P.zs i (P.zs i + P.xs i) = P.zs + unitVec i :=
      update_flip _ _ _ (by rw [ha])
    rw [e2, ha]
    simp only [if_neg (by decide : ¬ (1 : ZMod 2) = 0), dbl_one,
      add_comm (unitVec i), unitVec_add_self, add_zero, add_assoc,
      show (3 : ZMod 4) + 2 = 1 from by decide]
    rw [Pauli.toMat_phase P.ph 3, Pauli.toMat_phase P.ph 1, iPowC_three, iPowC_one,
      smul_smul, smul_smul]
    have c1 : (1 + Complex.I) / 2 * -Complex.I = (1 - Complex.I) / 2 := by
      linear_combination (-1/2 : ℂ) * Complex.I_sq
    have c2 : (1 - Complex.I) / 2 * Complex.I = (1 + Complex.I) / 2 := by
      linear_combination (-1/2 : ℂ) * Complex.I_sq
    rw [c1, c2]
    module

/-! ### CNOT -/

lemma cxMap_involutive {n : ℕ} {i j : Fin n} (h : i ≠ j) (x : Bits n) :
    cxMap i j (cxMap i j x) = x := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [cxMap, Function.update_of_ne h, zmod2_cancel]
  · simp [cxMap, Function.update_of_ne hk]

lemma cxMap_add {n : ℕ} (i j : Fin n) (x y : Bits n) :
    cxMap i j (x + y) = cxMap i j x + cxMap i j y := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [cxMap]; ring
  · simp [cxMap, Function.update_of_ne hk]

lemma dotB_cxMap {n : ℕ} (i j : Fin n) (b x : Bits n) :
    dotB b (cxMap i j x) = dotB (cxMap j i b) x := by
  rw [cxMap, cxMap, dotB_update_right, dotB_update_left]
  ring_nf
  simp [zmod2_two_eq_zero]

lemma cx_eq_iff {n : ℕ} {i j : Fin n} (h : i ≠ j) (y z : Bits n) :
    y = cxMap i j z ↔ z = cxMap i j y := by
  constructor
  · rintro rfl; rw [cxMap_involutive h]
  · rintro rfl; rw [cxMap_involutive h]

lemma cx_mul_right {n : ℕ} {i j : Fin n} (h : i ≠ j) (M : Matrix (Bits n) (Bits n) ℂ)
    (y x : Bits n) : (M * gateMat (Gate.CX i j h)) y x = M y (cxMap i j x) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (cxMap i j x)]
  · simp [gateMat]
  · intro z _ hz
    simp only [gateMat, Matrix.of_apply]
    rw [if_neg (fun hcon => hz hcon), mul_zero]
  · intro hc; exact absurd (Finset.mem_univ _) hc

lemma cx_mul_left {n : ℕ} {i j : Fin n} (h : i ≠ j) (M : Matrix (Bits n) (Bits n) ℂ)
    (y x : Bits n) : (gateMat (Gate.CX i j h) * M) y x = M (cxMap i j y) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (cxMap i j y)]
  · simp [gateMat, cxMap_involutive h]
  · intro z _ hz
    have hne : ¬ (y = cxMap i j z) := fun hcon => hz ((cx_eq_iff h y z).mp hcon)
    simp [gateMat, hne]
  · intro hc; exact absurd (Finset.mem_univ _) hc

lemma stepPauli_CX {n : ℕ} {i j : Fin n} (h : i ≠ j) (P : Pauli n) :
    stepPauli (Gate.CX i j h) P = ⟨P.ph, cxMap i j P.xs, cxMap j i P.zs⟩ := rfl

/-- Heisenberg update for CNOT, in commuted form. -/
lemma CX_comm {n : ℕ} {i j : Fin n} (h : i ≠ j) (P : Pauli n) :
    P.toMat * gateMat (Gate.CX i j h)
      = gateMat (Gate.CX i j h) * (stepPauli (Gate.CX i j h) P).toMat := by
  ext y x
  rw [cx_mul_right h, cx_mul_left h, stepPauli_CX]
  simp only [Pauli.toMat, Matrix.of_apply]
  rw [dotB_cxMap]
  by_cases hc : y = cxMap i j x + P.xs
  · have hc2 : cxMap i j y = x + cxMap i j P.xs := by
      rw [hc, cxMap_add, cxMap_involutive h]
    rw [if_pos hc, if_pos hc2]
  · have hc2 : ¬ (cxMap i j y = x + cxMap i j P.xs) := by
      intro hh
      apply hc
      have h3 := congrArg (cxMap i j) hh
      rwa [cxMap_involutive h, cxMap_add, cxMap_involutive h] at h3
    rw [if_neg hc, if_neg hc2]

lemma CX_selfadj {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (gateMat (Gate.CX i j h))ᴴ = gateMat (Gate.CX i j h) := by
  ext y x
  simp only [Matrix.conjTranspose_apply, gateMat, Matrix.of_apply]
  by_cases hc : y = cxMap i j x
  · rw [if_pos hc, if_pos ((cx_eq_iff h y x).mp hc)]; simp
  · rw [if_neg hc, if_neg (fun hcon => hc ((cx_eq_iff h x y).mp hcon))]; simp

lemma CX_mul_CX {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    gateMat (Gate.CX i j h) * gateMat (Gate.CX i j h) = 1 := by
  ext y x
  rw [cx_mul_left h]
  simp only [gateMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hc : y = x
  · subst hc; simp
  · rw [if_neg, if_neg hc]
    intro hcon
    have h3 := congrArg (cxMap i j) hcon
    rw [cxMap_involutive h, cxMap_involutive h] at h3
    exact hc h3

/-! ### Unitarity and the Heisenberg picture for a general gate -/

lemma gateMat_conjTranspose_mul_self {n : ℕ} (g : Gate n) :
    (gateMat g)ᴴ * gateMat g = 1 := by
  cases g with
  | H i => rw [H_selfadj]; exact H_mul_H i
  | S i => exact S_unitary i
  | CX i j h => rw [CX_selfadj h]; exact CX_mul_CX h

lemma gateMat_mul_conjTranspose {n : ℕ} (g : Gate n) :
    gateMat g * (gateMat g)ᴴ = 1 := by
  cases g with
  | H i => rw [H_selfadj]; exact H_mul_H i
  | S i => exact S_unitary' i
  | CX i j h => rw [CX_selfadj h]; exact CX_mul_CX h

/-- The Heisenberg update, in commuted form, for an arbitrary Clifford generator. -/
lemma gate_comm {n : ℕ} (g : Gate n) (P : Pauli n) :
    P.toMat * gateMat g = gateMat g * (stepPauli g P).toMat := by
  cases g with
  | H i => exact H_comm i P
  | S i => exact S_comm i P
  | CX i j h => exact CX_comm h P

/-- Heisenberg picture for a single gate: conjugating a Pauli operator by a Clifford gate
gives the Pauli operator computed by the tableau update. -/
theorem gate_conj_pauli {n : ℕ} (g : Gate n) (P : Pauli n) :
    (gateMat g)ᴴ * P.toMat * gateMat g = (stepPauli g P).toMat := by
  rw [Matrix.mul_assoc, gate_comm g P, ← Matrix.mul_assoc, gateMat_conjTranspose_mul_self,
    Matrix.one_mul]

/-! ## Circuits -/

lemma sgnC_zero : sgnC 0 = 1 := by simp [sgnC]

lemma circuitMat_conjTranspose_mul_self {n : ℕ} (C : List (Gate n)) :
    (circuitMat C)ᴴ * circuitMat C = 1 := by
  induction C with
  | nil => simp [circuitMat]
  | cons g gs ih =>
    simp only [circuitMat, Matrix.conjTranspose_mul]
    calc (gateMat g)ᴴ * (circuitMat gs)ᴴ * (circuitMat gs * gateMat g)
        = (gateMat g)ᴴ * ((circuitMat gs)ᴴ * circuitMat gs) * gateMat g := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [ih, Matrix.mul_one, gateMat_conjTranspose_mul_self]

/-- **Heisenberg evolution of Pauli operators under a stabilizer circuit.**
Conjugating any Pauli operator by the unitary of a Clifford circuit yields the Pauli operator
computed by the classical tableau simulation. -/
theorem circuit_conj_pauli {n : ℕ} (C : List (Gate n)) (P : Pauli n) :
    (circuitMat C)ᴴ * P.toMat * circuitMat C = (simulate C P).toMat := by
  induction C with
  | nil => simp [circuitMat, simulate]
  | cons g gs ih =>
    simp only [circuitMat, simulate, Matrix.conjTranspose_mul]
    calc (gateMat g)ᴴ * (circuitMat gs)ᴴ * P.toMat * (circuitMat gs * gateMat g)
        = (gateMat g)ᴴ * ((circuitMat gs)ᴴ * P.toMat * circuitMat gs) * gateMat g := by
          simp [Matrix.mul_assoc]
      _ = (gateMat g)ᴴ * (simulate gs P).toMat * gateMat g := by rw [ih]
      _ = (stepPauli g (simulate gs P)).toMat := gate_conj_pauli _ _

lemma Pauli.toMat_zero_zero {n : ℕ} (Q : Pauli n) : Q.toMat 0 0 = readout Q := by
  simp only [Pauli.toMat, Matrix.of_apply, readout, zero_add, dotB_zero_right, sgnC_zero, mul_one]
  by_cases h : Q.xs = 0
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]

/-- Expectation value of a Pauli observable in the output state of a stabilizer circuit
is computed by the classical simulation. -/
theorem circuit_expectation {n : ℕ} (C : List (Gate n)) (P : Pauli n) :
    ((circuitMat C)ᴴ * P.toMat * circuitMat C) 0 0 = readout (simulate C P) := by
  rw [circuit_conj_pauli, Pauli.toMat_zero_zero]

/-! ## Efficiency -/

/-- The instrumented simulator computes the tableau simulation. -/
lemma runInstr_fst {n : ℕ} (C : List (Gate n)) (P : Pauli n) :
    (runInstr C P).1 = simulate C P := by
  induction C with
  | nil => rfl
  | cons g gs ih => simp [runInstr, simulate, ih]

/-- The simulation cost is linear in the number of gates (in particular polynomial in the
number of qubits and the circuit size). -/
lemma runInstr_snd {n : ℕ} (C : List (Gate n)) (P : Pauli n) :
    (runInstr C P).2 = 3 * C.length := by
  induction C with
  | nil => rfl
  | cons g gs ih => simp [runInstr, ih]; ring

/-- Each gate update touches at most two of the `2n` tableau bits. -/
lemma stepPauli_local {n : ℕ} (g : Gate n) (P : Pauli n) :
    ((Finset.univ.filter
      (fun k => (stepPauli g P).xs k ≠ P.xs k ∨ (stepPauli g P).zs k ≠ P.zs k)).card) ≤ 2 := by
  have key : ∀ i j : Fin n,
      (Finset.univ.filter
        (fun k => (stepPauli g P).xs k ≠ P.xs k ∨ (stepPauli g P).zs k ≠ P.zs k))
        ⊆ ({i, j} : Finset (Fin n)) →
      ((Finset.univ.filter
        (fun k => (stepPauli g P).xs k ≠ P.xs k ∨ (stepPauli g P).zs k ≠ P.zs k)).card) ≤ 2 := by
    intro i j hsub
    refine le_trans (Finset.card_le_card hsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  cases g with
  | H i =>
    refine key i i ?_
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    rcases hk with hk | hk <;>
      exact hk (by simp [stepPauli, Function.update_of_ne hne.1])
  | S i =>
    refine key i i ?_
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    rcases hk with hk | hk
    · exact hk (by simp [stepPauli])
    · exact hk (by simp [stepPauli, Function.update_of_ne hne.1])
  | CX i j h =>
    refine key j i ?_
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    rcases hk with hk | hk
    · exact hk (by simp [stepPauli, Function.update_of_ne hne.1])
    · exact hk (by simp [stepPauli, Function.update_of_ne hne.2])

/-! ## Measurement statistics -/

/-- The probability of observing `0` on qubit `k` when measuring the output of a stabilizer
circuit in the computational basis is determined by a single classically simulated
Pauli expectation value. -/
theorem circuit_measure_prob {n : ℕ} (C : List (Gate n)) (k : Fin n) :
    ((∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0),
        ‖circuitMat C x 0‖ ^ 2 : ℝ) : ℂ)
      = (1 + readout (simulate C (Pauli.mk 0 0 (unitVec k)))) / 2 := by
  have hconj : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  set M := circuitMat C with hMdef
  set c : Bits n → ℂ := fun x => ((‖M x 0‖ ^ 2 : ℝ) : ℂ) with hcdef
  have hZ : (Pauli.mk 0 0 (unitVec k) : Pauli n).toMat
      = Matrix.diagonal (fun x : Bits n => sgnC (x k)) := by
    ext y x
    by_cases h : y = x
    · subst h; simp [Pauli.toMat, iPowC_zero, dotB_unit_left]
    · simp [Pauli.toMat, h]
  have htot : ∑ x : Bits n, c x = 1 := by
    have h0 : ((M)ᴴ * M) 0 0 = 1 := by rw [circuitMat_conjTranspose_mul_self C]; simp
    rw [Matrix.mul_apply] at h0
    rw [← h0]
    exact Finset.sum_congr rfl (fun x _ => (hconj (M x 0)).symm)
  have hsig : ∑ x : Bits n, sgnC (x k) * c x
      = readout (simulate C (Pauli.mk 0 0 (unitVec k))) := by
    have h1 : (Mᴴ * (Pauli.mk 0 0 (unitVec k) : Pauli n).toMat * M) 0 0
        = readout (simulate C (Pauli.mk 0 0 (unitVec k))) := circuit_expectation _ _
    rw [← h1, hZ, Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    show sgnC (x k) * ((‖M x 0‖ ^ 2 : ℝ) : ℂ) = _
    rw [← hconj (M x 0)]
    ring
  have e1 : ∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), sgnC (x k) * c x
      = ∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), c x := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_filter] at hx
    rw [hx.2, sgnC_zero, one_mul]
  have e2 : ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), sgnC (x k) * c x
      = -∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), c x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_filter] at hx
    rw [sgnC, if_neg hx.2]
    ring
  have hsplit : ∑ x : Bits n, c x
      = (∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), c x)
        + ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), c x :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsplit2 : ∑ x : Bits n, sgnC (x k) * c x
      = (∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), c x)
        - ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), c x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Bits n => x k = 0)
      (fun x => sgnC (x k) * c x), e1, e2]
    ring
  rw [Complex.ofReal_sum]
  rw [hsplit] at htot
  rw [hsplit2] at hsig
  linear_combination (1/2 : ℂ) * htot + (1/2 : ℂ) * hsig

/-! ## The gate matrices are the standard ones

These lemmas confirm that `gateMat` really is the usual Hadamard, phase and CNOT matrix in the
computational basis, so that the statements above are about genuine quantum circuits. -/

/-- The phase gate is `diag (1, i)` on qubit `i`. -/
lemma gateMat_S_diagonal {n : ℕ} (i : Fin n) :
    gateMat (Gate.S i) = Matrix.diagonal (fun x : Bits n => if x i = 0 then 1 else Complex.I) := by
  ext y x
  by_cases h : y = x
  · subst h
    rcases zmod2_cases (y i) with hb | hb <;>
      simp [gateMat, Zp, Pauli.toMat, iPowC_zero, dotB_unit_left, hb, sgnC] <;> ring
  · simp [gateMat, Zp, Pauli.toMat, h]

/-- The Hadamard gate acts as `2^(-1/2) (-1)^(y i * x i)` on qubit `i` and as the identity on the
other qubits. -/
lemma gateMat_H_apply {n : ℕ} (i : Fin n) (y x : Bits n) :
    gateMat (Gate.H i) y x =
      if (∀ k, k ≠ i → y k = x k) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * sgnC (y i * x i) else 0 := by
  simp only [gateMat, Matrix.smul_apply, Matrix.add_apply, Xp, Zp, Pauli.toMat, Matrix.of_apply,
    iPowC_zero, dotB_zero_left, dotB_unit_left, one_mul, sgnC_zero, smul_eq_mul, add_zero]
  by_cases hagree : ∀ k, k ≠ i → y k = x k
  · rw [if_pos hagree]
    have hEq : (y = x) ↔ (y i = x i) := by
      constructor
      · intro h; rw [h]
      · intro h
        funext k
        by_cases hk : k = i
        · subst hk; exact h
        · exact hagree k hk
    have hSh : (y = x + unitVec i) ↔ (y i = x i + 1) := by
      constructor
      · intro h; have h2 := congrFun h i; simpa [unitVec_self] using h2
      · intro h
        funext k
        by_cases hk : k = i
        · subst hk; simpa [unitVec_self] using h
        · simp [unitVec, Pi.single_eq_of_ne hk, hagree k hk]
    rcases zmod2_cases (y i) with hy | hy <;> rcases zmod2_cases (x i) with hx | hx <;>
      simp [hEq, hSh, hy, hx, sgnC, show (1 + 1 : ZMod 2) = 0 from by decide]
  · push_neg at hagree
    obtain ⟨k, hk, hne⟩ := hagree
    have h1 : ¬ (y = x + unitVec i) := by
      intro hh
      exact hne (by have h2 := congrFun hh k; simpa [unitVec, Pi.single_eq_of_ne hk] using h2)
    have h2 : ¬ (y = x) := fun hh => hne (by rw [hh])
    rw [if_neg h1, if_neg h2, if_neg]
    · simp
    · push_neg
      exact ⟨k, hk, hne⟩

/-- CNOT is the permutation matrix `|x⟩ ↦ |x with x j replaced by x j + x i⟩`. -/
lemma gateMat_CX_apply {n : ℕ} {i j : Fin n} (h : i ≠ j) (y x : Bits n) :
    gateMat (Gate.CX i j h) y x = if y = Function.update x j (x j + x i) then 1 else 0 := rfl

/-! ## Gottesman–Knill -/

/-- **Gottesman–Knill theorem.**  Stabilizer circuits are efficiently classically simulable.

For every stabilizer circuit `C` (a list of Hadamard, phase and CNOT gates on `n` qubits):

1. conjugation of any Pauli operator by the `2^n × 2^n` unitary of `C` is exactly reproduced by
   the classical tableau update `simulate C`, which is computed by an explicit algorithm
   (`runInstr`) using a number of elementary register updates linear in the circuit size, each
   update touching at most two of the `2n` tableau bits;
2. the expectation value of any Pauli observable in the output state `C |0…0⟩` is read off from
   the simulated tableau in constant time;
3. consequently the outcome probabilities of computational-basis measurements are computed
   classically from the simulation.

The gate matrices `gateMat` are the standard ones (see `gateMat_H_apply`, `gateMat_S_diagonal`
and `gateMat_CX_apply`), and `Pauli.toMat` is the usual matrix `i^ph X^xs Z^zs` of a Pauli group
element, so all statements are about genuine `2^n × 2^n` quantum circuits. -/
theorem gottesman_knill {n : ℕ} (C : List (Gate n)) (P : Pauli n) (k : Fin n) :
    -- (1) the tableau simulation is exact, and is computed in time linear in the circuit size
    (circuitMat C)ᴴ * P.toMat * circuitMat C = (simulate C P).toMat ∧
    (runInstr C P).1 = simulate C P ∧
    (runInstr C P).2 = 3 * C.length ∧
    (∀ g : Gate n, ∀ Q : Pauli n, ((Finset.univ.filter
      (fun m => (stepPauli g Q).xs m ≠ Q.xs m ∨ (stepPauli g Q).zs m ≠ Q.zs m)).card) ≤ 2) ∧
    -- (2) Pauli expectation values of the output state are read off from the tableau
    ((circuitMat C)ᴴ * P.toMat * circuitMat C) 0 0 = readout (simulate C P) ∧
    -- (3) measurement probabilities are computed classically
    ((∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0),
        ‖circuitMat C x 0‖ ^ 2 : ℝ) : ℂ)
      = (1 + readout (simulate C (Pauli.mk 0 0 (unitVec k)))) / 2 :=
  ⟨circuit_conj_pauli C P, runInstr_fst C P, runInstr_snd C P,
    fun g Q => stepPauli_local g Q, circuit_expectation C P, circuit_measure_prob C k⟩

end QI

