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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

/-! ## Basis states and tensor products of one-qubit operators -/

/-- A computational basis state of `n` qubits. -/
abbrev BasisState (n : ℕ) := Fin n → Bool

/-- An operator on `n` qubits, as a `2^n × 2^n` complex matrix. -/
abbrev Op (n : ℕ) := Matrix (BasisState n) (BasisState n) ℂ

/-- The tensor product `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (n-1)` of one-qubit operators. -/
def tens {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) : Op n :=
  Matrix.of fun a b => ∏ j, f j (a j) (b j)

@[simp] lemma tens_apply {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) (a b : BasisState n) :
    tens f a b = ∏ j, f j (a j) (b j) := rfl

lemma tens_mul {n : ℕ} (f g : Fin n → Matrix Bool Bool ℂ) :
    tens f * tens g = tens (fun j => f j * g j) := by
  ext a b
  simp only [Matrix.mul_apply, tens_apply]
  have h : ∀ c : BasisState n, (∏ j, f j (a j) (c j)) * (∏ j, g j (c j) (b j))
      = ∏ j, (f j (a j) (c j) * g j (c j) (b j)) := by
    intro c; rw [Finset.prod_mul_distrib]
  simp only [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext a b
  simp only [tens_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

lemma tens_conjTranspose {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) :
    (tens f)ᴴ = tens (fun j => (f j)ᴴ) := by
  ext a b
  simp [Matrix.conjTranspose_apply]

lemma tens_update_smul {n : ℕ} (f : Fin n → Matrix Bool Bool ℂ) (k : Fin n) (c : ℂ)
    (M : Matrix Bool Bool ℂ) :
    tens (Function.update f k (c • M)) = c • tens (Function.update f k M) := by
  ext a b
  simp only [tens_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have key : ∀ j ∈ Finset.univ.erase k,
      (Function.update f k (c • M)) j (a j) (b j) = (Function.update f k M) j (a j) (b j) := by
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
  rw [Finset.prod_congr rfl key]
  simp only [Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## One-qubit matrices -/

/-- `1/√2`, as a complex number. -/
noncomputable def isqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma isqrt2_sq : isqrt2 * isqrt2 = 1 / 2 := by
  simp only [isqrt2, ← Complex.ofReal_mul]
  rw [show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = ((Real.sqrt 2) * (Real.sqrt 2))⁻¹ by ring]
  rw [Real.mul_self_sqrt (by norm_num)]
  norm_num

@[simp] lemma conj_isqrt2 : (starRingEnd ℂ) isqrt2 = isqrt2 := by
  simp [isqrt2]

/-- The Pauli `X` matrix. -/
def mX : Matrix Bool Bool ℂ := Matrix.of fun a b => if a = !b then 1 else 0

/-- The Pauli `Z` matrix. -/
def mZ : Matrix Bool Bool ℂ := Matrix.of fun a b => if a = b then (if b then -1 else 1) else 0

/-- The Hadamard matrix. -/
noncomputable def mH : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => (if a && b then -1 else 1) * isqrt2

/-- The phase gate `S = diag (1, i)`. -/
noncomputable def mS : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then (if b then Complex.I else 1) else 0

/-- The one-qubit Pauli operator `X^x Z^z`. -/
noncomputable def p1 (x z : Bool) : Matrix Bool Bool ℂ :=
  (if x then mX else 1) * (if z then mZ else 1)

lemma p1_apply (x z a b : Bool) :
    p1 x z a b = (if a = xor b x then 1 else 0) * (if z && b then -1 else 1) := by
  cases x <;> cases z <;> cases a <;> cases b <;>
    simp [p1, mX, mZ, Matrix.mul_apply, Matrix.one_apply]

/-! ## Powers of `i` -/

/-- `i ^ c` for `c : ZMod 4`. -/
noncomputable def iPow (c : ZMod 4) : ℂ := Complex.I ^ c.val

@[simp] lemma iPow_zero : iPow 0 = 1 := by simp [iPow]

lemma iPow_two : iPow 2 = -1 := by
  simp [iPow, show (2 : ZMod 4).val = 2 from rfl, Complex.I_sq]

lemma iPow_three : iPow 3 = -Complex.I := by
  simp [iPow, show (3 : ZMod 4).val = 3 from rfl, pow_succ]

lemma iPow_add (a b : ZMod 4) : iPow (a + b) = iPow a * iPow b := by
  simp only [iPow, ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) 4]
  rw [pow_add, pow_mul]
  norm_num [Complex.I_pow_four]

lemma iPow_ne_zero (a : ZMod 4) : iPow a ≠ 0 := by simp [iPow, Complex.I_ne_zero]

lemma iPow_one : iPow 1 = Complex.I := by simp [iPow, show (1 : ZMod 4).val = 1 from rfl]

/-! ## Pauli operators on `n` qubits -/

/-- A Pauli operator on `n` qubits: the phase `i^ph` times `⨂ⱼ X^{xⱼ} Z^{zⱼ}`. -/
structure Pauli (n : ℕ) where
  /-- The power of `i` in front of the operator. -/
  ph : ZMod 4
  /-- The `X`-part. -/
  x : BasisState n
  /-- The `Z`-part. -/
  z : BasisState n

/-- The matrix of a Pauli operator. -/
noncomputable def pauliMat {n : ℕ} (p : Pauli n) : Op n :=
  iPow p.ph • tens (fun j => p1 (p.x j) (p.z j))

/-- The sign `(-1)^{z ⬝ b}`, as a rational number. -/
def sgnQ {n : ℕ} (z b : BasisState n) : ℚ := ∏ j, (if z j && b j then -1 else 1)

lemma sgnQ_eq_pm {n : ℕ} (z b : BasisState n) : sgnQ z b = 1 ∨ sgnQ z b = -1 := by
  classical
  unfold sgnQ
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => left; simp
  | insert j s hj ih =>
      rw [Finset.prod_insert hj]
      rcases ih with h | h <;> rw [h] <;>
        [skip; skip] <;> by_cases hz : z j && b j <;> simp [hz]

lemma sgnQ_ne_zero {n : ℕ} (z b : BasisState n) : (sgnQ z b : ℂ) ≠ 0 := by
  rcases sgnQ_eq_pm z b with h | h <;> rw [h] <;> norm_num

lemma pauliMat_apply {n : ℕ} (p : Pauli n) (a b : BasisState n) :
    pauliMat p a b =
      if (∀ j, a j = xor (b j) (p.x j)) then iPow p.ph * ((sgnQ p.z b : ℚ) : ℂ) else 0 := by
  have hprod : ∀ j : Fin n, p1 (p.x j) (p.z j) (a j) (b j)
      = (if a j = xor (b j) (p.x j) then 1 else 0) * (if p.z j && b j then (-1 : ℂ) else 1) :=
    fun j => p1_apply _ _ _ _
  simp only [pauliMat, Matrix.smul_apply, smul_eq_mul, tens_apply, hprod]
  rw [Finset.prod_mul_distrib]
  by_cases h : ∀ j, a j = xor (b j) (p.x j)
  · rw [if_pos h]
    have h1 : (∏ j, if a j = xor (b j) (p.x j) then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one (fun j _ => by rw [if_pos (h j)])
    rw [h1, one_mul]
    congr 1
    simp only [sgnQ, Rat.cast_prod]
    exact Finset.prod_congr rfl (fun j _ => by by_cases hz : p.z j && b j <;> simp [hz])
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    have : (∏ j, if a j = xor (b j) (p.x j) then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])
    rw [this, zero_mul, mul_zero]

/-! ## Clifford gates -/

/-- The generating Clifford gates: Hadamard, phase, and controlled-`Z`. -/
inductive Gate (n : ℕ)
  | H (k : Fin n) : Gate n
  | S (k : Fin n) : Gate n
  | CZ (k l : Fin n) (h : k ≠ l) : Gate n

/-- The unitary matrix of a gate. -/
noncomputable def gateMat {n : ℕ} : Gate n → Op n
  | Gate.H k => tens (Function.update (fun _ => 1) k mH)
  | Gate.S k => tens (Function.update (fun _ => 1) k mS)
  | Gate.CZ k l _ => Matrix.diagonal (fun a => if a k && a l then -1 else 1)

/-- The classical (tableau) update of a Pauli operator under conjugation by a gate:
`step g p` is the Pauli `G† P G`. -/
def step {n : ℕ} : Gate n → Pauli n → Pauli n
  | Gate.H k, p =>
      { ph := p.ph + (if p.x k && p.z k then 2 else 0)
        x := Function.update p.x k (p.z k)
        z := Function.update p.z k (p.x k) }
  | Gate.S k, p =>
      { ph := p.ph + (if p.x k then 3 else 0)
        x := p.x
        z := Function.update p.z k (xor (p.z k) (p.x k)) }
  | Gate.CZ k l _, p =>
      { ph := p.ph + (if p.x k && p.x l then 2 else 0)
        x := p.x
        z := Function.update (Function.update p.z k (xor (p.z k) (p.x l))) l
              (xor (p.z l) (p.x k)) }

/-! ## One-qubit conjugation identities -/

lemma mH_conj (x z : Bool) :
    iPow (if x && z then 2 else 0) • (mH * p1 z x) = p1 x z * mH := by
  have h2 : iPow 2 = -1 := iPow_two
  cases x <;> cases z <;>
    (ext a b; cases a <;> cases b <;>
      simp [p1, mX, mZ, mH, Matrix.mul_apply, Matrix.one_apply, h2])

lemma mS_conj (x z : Bool) :
    iPow (if x then 3 else 0) • (mS * p1 x (xor z x)) = p1 x z * mS := by
  have h3 : iPow 3 = -Complex.I := iPow_three
  cases x <;> cases z <;>
    (ext a b; cases a <;> cases b <;>
      simp [p1, mX, mZ, mS, Matrix.mul_apply, Matrix.one_apply, h3])

lemma mH_unitary : mHᴴ * mH = 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [mH, Matrix.mul_apply, Matrix.conjTranspose_apply, isqrt2_sq]
  ring_nf

lemma mS_unitary : mSᴴ * mS = 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [mS, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-! ## Gate conjugation on `n` qubits -/

/-- Generic intertwining relation for a one-qubit gate `G` acting on qubit `k`. -/
lemma single_qubit_intertwine {n : ℕ} (k : Fin n) (G : Matrix Bool Bool ℂ) (p : Pauli n)
    (d : ZMod 4) (x' z' : Bool)
    (hG : iPow d • (G * p1 x' z') = p1 (p.x k) (p.z k) * G) :
    tens (Function.update (fun _ => 1) k G) *
        pauliMat ⟨p.ph + d, Function.update p.x k x', Function.update p.z k z'⟩
      = pauliMat p * tens (Function.update (fun _ => 1) k G) := by
  set F : Fin n → Matrix Bool Bool ℂ := fun j => p1 (p.x j) (p.z j) with hF
  have hleft : (fun j => (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j *
      p1 ((Function.update p.x k x') j) ((Function.update p.z k z') j))
      = Function.update F k (G * p1 x' z') := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [Function.update_self, hF]
    · simp [Function.update_of_ne hj, hF]
  have hright : (fun j => p1 (p.x j) (p.z j) *
      (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j)
      = Function.update F k (p1 (p.x k) (p.z k) * G) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [Function.update_self, hF]
    · simp [Function.update_of_ne hj, hF]
  simp only [pauliMat, Matrix.mul_smul, Matrix.smul_mul, tens_mul, hleft, hright, iPow_add]
  rw [← hG, tens_update_smul, smul_smul]

lemma sgnQ_update {n : ℕ} (z b : BasisState n) (k : Fin n) (v : Bool) :
    sgnQ (Function.update z k v) b = (if xor v (z k) && b k then -1 else 1) * sgnQ z b := by
  unfold sgnQ
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have key : ∀ j ∈ Finset.univ.erase k,
      (if (Function.update z k v) j && b j then (-1 : ℚ) else 1)
        = (if z j && b j then (-1 : ℚ) else 1) := by
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [Finset.prod_congr rfl key, Function.update_self, ← mul_assoc]
  congr 1
  cases v <;> cases hz : z k <;> cases hb : b k <;> norm_num

lemma cz_intertwine {n : ℕ} (k l : Fin n) (hkl : k ≠ l) (p : Pauli n) :
    gateMat (Gate.CZ k l hkl) * pauliMat (step (Gate.CZ k l hkl) p)
      = pauliMat p * gateMat (Gate.CZ k l hkl) := by
  ext a b
  have hx : (step (Gate.CZ k l hkl) p).x = p.x := rfl
  have hsgn : sgnQ (step (Gate.CZ k l hkl) p).z b
      = (if p.x k && b l then -1 else 1) * ((if p.x l && b k then -1 else 1) * sgnQ p.z b) := by
    show sgnQ (Function.update (Function.update p.z k (xor (p.z k) (p.x l))) l
      (xor (p.z l) (p.x k))) b = _
    rw [sgnQ_update, sgnQ_update, Function.update_of_ne (Ne.symm hkl)]
    congr 2
    · cases hzl : p.z l <;> cases hxk : p.x k <;> simp
    · cases hzk : p.z k <;> cases hxl : p.x l <;> simp
  have hph : iPow (step (Gate.CZ k l hkl) p).ph
      = iPow p.ph * (if p.x k && p.x l then -1 else 1) := by
    show iPow (p.ph + (if p.x k && p.x l then 2 else 0)) = _
    rw [iPow_add]
    by_cases h : p.x k && p.x l <;> simp [h, iPow_two]
  simp only [gateMat, Matrix.diagonal_mul, Matrix.mul_diagonal, pauliMat_apply, hx]
  by_cases h : ∀ j, a j = xor (b j) (p.x j)
  · rw [if_pos h, if_pos h, hsgn, hph]
    rw [h k, h l]
    push_cast
    cases hxk : p.x k <;> cases hxl : p.x l <;> cases hbk : b k <;> cases hbl : b l <;> simp
  · rw [if_neg h, if_neg h, mul_zero, zero_mul]

lemma gate_intertwine {n : ℕ} (g : Gate n) (p : Pauli n) :
    gateMat g * pauliMat (step g p) = pauliMat p * gateMat g := by
  match g with
  | Gate.H k =>
      exact single_qubit_intertwine k mH p _ _ _ (mH_conj (p.x k) (p.z k))
  | Gate.S k =>
      have h := single_qubit_intertwine k mS p (if p.x k then 3 else 0) (p.x k)
        (xor (p.z k) (p.x k)) (by
          have := mS_conj (p.x k) (p.z k)
          simpa [Bool.xor_comm] using this)
      simpa [gateMat, step, Function.update_eq_self_iff] using h
  | Gate.CZ k l hkl => exact cz_intertwine k l hkl p

/-- A one-qubit unitary tensored with identities is unitary. -/
lemma tens_single_unitary {n : ℕ} (k : Fin n) (G : Matrix Bool Bool ℂ) (hG : Gᴴ * G = 1) :
    (tens (Function.update (fun _ => 1) k G))ᴴ * tens (Function.update (fun _ => 1) k G)
      = (1 : Op n) := by
  rw [tens_conjTranspose, tens_mul]
  have h : (fun j => ((Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j)ᴴ *
      (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j)
      = fun _ : Fin n => (1 : Matrix Bool Bool ℂ) := by
    funext j
    by_cases hj : j = k
    · subst hj; simpa using hG
    · simp [Function.update_of_ne hj]
  rw [h, tens_one]

lemma gate_unitary {n : ℕ} (g : Gate n) : (gateMat g)ᴴ * gateMat g = 1 := by
  match g with
  | Gate.H k => exact tens_single_unitary k mH mH_unitary
  | Gate.S k => exact tens_single_unitary k mS mS_unitary
  | Gate.CZ k l _ =>
      simp only [gateMat, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext a
      by_cases h : a k = true ∧ a l = true <;> simp [Bool.and_eq_true, h]

/-! ## Circuits -/

/-- The unitary of a circuit; the head of the list is applied first. -/
noncomputable def circMat {n : ℕ} : List (Gate n) → Op n
  | [] => 1
  | g :: C => circMat C * gateMat g

/-- The classical simulation of a circuit acting on a Pauli operator (Heisenberg picture). -/
def simulate {n : ℕ} : List (Gate n) → Pauli n → Pauli n
  | [], p => p
  | g :: C, p => step g (simulate C p)

lemma circ_intertwine {n : ℕ} (C : List (Gate n)) (p : Pauli n) :
    circMat C * pauliMat (simulate C p) = pauliMat p * circMat C := by
  induction C with
  | nil => simp [circMat, simulate]
  | cons g C ih =>
      simp only [circMat, simulate]
      rw [Matrix.mul_assoc, gate_intertwine, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

lemma circ_unitary {n : ℕ} (C : List (Gate n)) : (circMat C)ᴴ * circMat C = 1 := by
  induction C with
  | nil => simp [circMat]
  | cons g C ih =>
      simp only [circMat, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (circMat C)ᴴ, ih, Matrix.one_mul,
        gate_unitary]

/-! ## The statement -/

/-- The Pauli `Z` on qubit `k`. -/
def pauliZ {n : ℕ} (k : Fin n) : Pauli n :=
  { ph := 0, x := fun _ => false, z := fun j => decide (j = k) }

/-- The probability that measuring qubit `k` of the state `U_C |b⟩` yields the outcome `0`. -/
noncomputable def measProb {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) : ℝ :=
  ∑ a : BasisState n, if a k then 0 else ‖circMat C a b‖ ^ 2

/-- `i^c` as a rational number, for the (Hermitian) case `c ∈ {0, 2}`. -/
def phaseQ (c : ZMod 4) : ℚ := if c = 0 then 1 else if c = 2 then -1 else 0

/-- A power of `i` that is real is `±1`, and then agrees with `phaseQ`. -/
lemma iPow_real_eq (c : ZMod 4) (h : (starRingEnd ℂ) (iPow c) = iPow c) :
    iPow c = ((phaseQ c : ℚ) : ℂ) := by
  have hc : ∀ d : ZMod 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
  rcases hc c with rfl | rfl | rfl | rfl
  · simp [phaseQ]
  · exfalso
    rw [iPow_one] at h
    simp at h
    exact Complex.I_ne_zero (by linear_combination -h / 2)
  · rw [iPow_two]
    norm_num [phaseQ, show (2 : ZMod 4) ≠ 0 by decide]
  · exfalso
    rw [iPow_three] at h
    simp at h
    exact Complex.I_ne_zero (by linear_combination h / 2)

/-- The value `⟨b| U† Zₖ U |b⟩` as computed by the classical tableau algorithm. -/
def classicalExp {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) : ℚ :=
  if ∀ j, (simulate C (pauliZ k)).x j = false then
    phaseQ (simulate C (pauliZ k)).ph * sgnQ (simulate C (pauliZ k)).z b
  else 0

/-- The classical simulation algorithm: it computes, by tableau updates only, the probability
that measuring qubit `k` at the end of the circuit `C` applied to `|b⟩` yields `0`. -/
def classicalProb {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) : ℚ :=
  (1 + classicalExp C b k) / 2

/-- The cost, in elementary bit operations, of the tableau update for one gate. -/
def stepCost {n : ℕ} : Gate n → ℕ
  | Gate.H _ => 3
  | Gate.S _ => 3
  | Gate.CZ _ _ _ => 3

/-- The number of elementary bit operations used by `classicalProb`: the tableau updates for
the gates, plus a final scan of the `n` qubits. -/
def simCost {n : ℕ} (C : List (Gate n)) : ℕ := (C.map stepCost).sum + (2 * n + 2)

lemma simCost_eq {n : ℕ} (C : List (Gate n)) : simCost C = 3 * C.length + 2 * n + 2 := by
  unfold simCost
  induction C with
  | nil => simp
  | cons g C ih =>
      cases g <;>
        simp only [List.map_cons, List.sum_cons, List.length_cons, stepCost] <;> omega

/-! ### The Pauli `Z` observable and the expectation value -/

lemma pauliZ_mat {n : ℕ} (k : Fin n) :
    pauliMat (pauliZ k) = Matrix.diagonal (fun a : BasisState n => if a k then -1 else 1) := by
  ext a b
  have hsgn : sgnQ (fun j => decide (j = k)) b = if b k then -1 else 1 := by
    unfold sgnQ
    rw [Finset.prod_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [pauliMat_apply, Matrix.diagonal_apply]
  show (if (∀ j, a j = xor (b j) false) then _ else _) = _
  by_cases h : a = b
  · subst h
    rw [if_pos (fun j => by simp), if_pos rfl]
    simp only [pauliZ, iPow_zero, one_mul, hsgn]
    by_cases hb : a k <;> simp [hb]
  · rw [if_neg h]
    refine if_neg ?_
    intro hall
    exact h (funext fun j => by simpa using hall j)

/-- The Heisenberg-evolved observable `U† Zₖ U` is exactly the Pauli produced by the classical
tableau simulation. -/
lemma conj_pauliZ {n : ℕ} (C : List (Gate n)) (k : Fin n) :
    (circMat C)ᴴ * pauliMat (pauliZ k) * circMat C = pauliMat (simulate C (pauliZ k)) := by
  rw [Matrix.mul_assoc, ← circ_intertwine C (pauliZ k), ← Matrix.mul_assoc, circ_unitary,
    Matrix.one_mul]

lemma pauliZ_mat_hermitian {n : ℕ} (k : Fin n) : (pauliMat (pauliZ k))ᴴ = pauliMat (pauliZ k) := by
  rw [pauliZ_mat, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : a k <;> simp [h]

lemma sim_hermitian {n : ℕ} (C : List (Gate n)) (k : Fin n) :
    (pauliMat (simulate C (pauliZ k)))ᴴ = pauliMat (simulate C (pauliZ k)) := by
  rw [← conj_pauliZ C k]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    pauliZ_mat_hermitian, Matrix.mul_assoc]

/-- The diagonal entry of the evolved Pauli is the rational number computed classically. -/
lemma pauli_diag_eq {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) :
    pauliMat (simulate C (pauliZ k)) b b = ((classicalExp C b k : ℚ) : ℂ) := by
  set q := simulate C (pauliZ k) with hq
  rw [pauliMat_apply, classicalExp, ← hq]
  by_cases h : ∀ j, q.x j = false
  · have hcond : ∀ j, b j = xor (b j) (q.x j) := by intro j; rw [h j]; simp
    rw [if_pos hcond, if_pos h]
    have hherm : (starRingEnd ℂ) (pauliMat q b b) = pauliMat q b b := by
      have := sim_hermitian C k
      have h2 : (pauliMat q)ᴴ b b = pauliMat q b b := by rw [this]
      simpa [Matrix.conjTranspose_apply] using h2
    rw [pauliMat_apply, if_pos hcond] at hherm
    have hs : ((sgnQ q.z b : ℚ) : ℂ) ≠ 0 := sgnQ_ne_zero _ _
    have hconj : (starRingEnd ℂ) (iPow q.ph) = iPow q.ph := by
      rw [map_mul, (by simp : (starRingEnd ℂ) ((sgnQ q.z b : ℚ) : ℂ) = ((sgnQ q.z b : ℚ) : ℂ))]
        at hherm
      exact mul_right_cancel₀ hs hherm
    rw [iPow_real_eq q.ph hconj]
    push_cast
    ring
  · have hcond : ¬ (∀ j, b j = xor (b j) (q.x j)) := by
      intro hall
      apply h
      intro j
      have := hall j
      cases hqj : q.x j
      · rfl
      · rw [hqj] at this; simp at this
    rw [if_neg hcond, if_neg h]
    simp

lemma star_mul_self_ofReal (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-- Total probability: the state `U_C |b⟩` is normalised. -/
lemma sum_normSq {n : ℕ} (C : List (Gate n)) (b : BasisState n) :
    ∑ a : BasisState n, ‖circMat C a b‖ ^ 2 = 1 := by
  have h1 : ((circMat C)ᴴ * circMat C) b b = 1 := by
    rw [circ_unitary]; simp
  rw [Matrix.mul_apply] at h1
  have h2 : ∀ a : BasisState n,
      (circMat C)ᴴ b a * circMat C a b = ((‖circMat C a b‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Matrix.conjTranspose_apply, star_mul_self_ofReal]
  rw [Finset.sum_congr rfl (fun a _ => h2 a)] at h1
  exact_mod_cast h1

/-- The expectation value of `Zₖ` in the output state equals the classically computed value. -/
lemma sum_signed_normSq {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) :
    ∑ a : BasisState n, (if a k then (-1 : ℝ) else 1) * ‖circMat C a b‖ ^ 2
      = ((classicalExp C b k : ℚ) : ℝ) := by
  have h1 := conj_pauliZ C k
  rw [pauliZ_mat] at h1
  have h2 : ((circMat C)ᴴ * (Matrix.diagonal (fun a : BasisState n => if a k then -1 else 1) :
      Op n) * circMat C) b b = ((classicalExp C b k : ℚ) : ℂ) := by
    rw [h1, pauli_diag_eq]
  rw [Matrix.mul_apply] at h2
  have h3 : ∀ a : BasisState n,
      ((circMat C)ᴴ * (Matrix.diagonal (fun a : BasisState n => if a k then -1 else 1) : Op n))
          b a * circMat C a b
        = (((if a k then (-1 : ℝ) else 1) * ‖circMat C a b‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    have : star (circMat C a b) * circMat C a b = ((‖circMat C a b‖ ^ 2 : ℝ) : ℂ) :=
      star_mul_self_ofReal _
    by_cases h : a k
    · rw [if_pos h, if_pos h]
      push_cast
      rw [mul_comm (star (circMat C a b)) (-1 : ℂ), mul_assoc, this]
      push_cast
      ring
    · rw [if_neg h, if_neg h]
      push_cast
      rw [mul_one, this]
      push_cast
      ring
  rw [Finset.sum_congr rfl (fun a _ => h3 a)] at h2
  exact_mod_cast h2

/-- **Gottesman–Knill**: stabilizer circuits are efficiently classically simulable.

For every `n`-qubit stabilizer (Clifford) circuit `C` built from Hadamard, phase and
controlled-`Z` gates, every computational basis input `|b⟩` and every qubit `k`, the exact
quantum probability that measuring qubit `k` of the output state `U_C |b⟩` yields the outcome
`0` — computed from the genuine `2^n × 2^n` complex unitary `U_C` — is equal to the rational
number produced by the purely classical tableau algorithm `classicalProb`, whose running cost
`simCost C` is linear (hence polynomial) in the number of gates and the number of qubits. -/
theorem gottesman_knill {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) :
    measProb C b k = ((classicalProb C b k : ℚ) : ℝ) ∧
      simCost C ≤ 3 * C.length + 2 * n + 2 := by
  refine ⟨?_, le_of_eq (simCost_eq C)⟩
  have hsplit : ∑ a : BasisState n, (if a k then (0 : ℝ) else ‖circMat C a b‖ ^ 2)
      = ((∑ a : BasisState n, ‖circMat C a b‖ ^ 2)
          + ∑ a : BasisState n, (if a k then (-1 : ℝ) else 1) * ‖circMat C a b‖ ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : a k <;> simp [h]
  rw [measProb, hsplit, sum_normSq, sum_signed_normSq, classicalProb]
  push_cast
  ring

end QI

