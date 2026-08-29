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
open scoped Matrix

namespace QI

/-! ## Bit vectors -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Bitwise `xor` of two bit strings. -/
def bxor (x y : Bits n) : Bits n := fun i => xor (x i) (y i)

/-- The bit string which is `c` at coordinate `j` and `false` elsewhere. -/
def condVec (c : Bool) (j : Fin n) : Bits n := fun i => c && decide (i = j)

@[simp] lemma bxor_apply (x y : Bits n) (i : Fin n) : bxor x y i = xor (x i) (y i) := rfl

@[simp] lemma condVec_apply (c : Bool) (j : Fin n) (i : Fin n) :
    condVec c j i = (c && decide (i = j)) := rfl

@[simp] lemma condVec_self (c : Bool) (j : Fin n) : condVec c j j = c := by
  simp [condVec]

lemma condVec_of_ne {c : Bool} {j i : Fin n} (h : i ≠ j) : condVec c j i = false := by
  simp [condVec, h]

lemma bxor_comm (x y : Bits n) : bxor x y = bxor y x := by
  funext i; simp [Bool.xor_comm]

lemma bxor_assoc (x y z : Bits n) : bxor (bxor x y) z = bxor x (bxor y z) := by
  funext i; simp

@[simp] lemma bxor_self (x : Bits n) : bxor x x = (fun _ => false) := by
  funext i; simp

@[simp] lemma bxor_cancel_right (x y : Bits n) : bxor (bxor x y) y = x := by
  funext i; simp

@[simp] lemma bxor_cancel_left (x y : Bits n) : bxor x (bxor x y) = y := by
  funext i; simp

lemma bxor_eq_iff {x y z : Bits n} : bxor x y = z ↔ x = bxor z y := by
  constructor <;> rintro rfl <;> simp

/-! ## Signs -/

/-- The sign `(-1)^(a·b)` of a single pair of bits. -/
def sgn1 (a b : Bool) : ℂ := if a && b then -1 else 1

/-- The sign `(-1)^(z·b)` attached to a `Z`-type Pauli acting on a basis vector. -/
def sgn (z b : Bits n) : ℂ := ∏ i, sgn1 (z i) (b i)

lemma sgn1_comm (a b : Bool) : sgn1 a b = sgn1 b a := by
  cases a <;> cases b <;> rfl

lemma sgn1_xor_right (a b c : Bool) : sgn1 a (xor b c) = sgn1 a b * sgn1 a c := by
  cases a <;> cases b <;> cases c <;> norm_num [sgn1]

lemma sgn_bxor_right (z b c : Bits n) : sgn z (bxor b c) = sgn z b * sgn z c := by
  simp only [sgn, bxor_apply, sgn1_xor_right]
  exact Finset.prod_mul_distrib

lemma sgn1_xor_left (a b c : Bool) : sgn1 (xor a b) c = sgn1 a c * sgn1 b c := by
  cases a <;> cases b <;> cases c <;> norm_num [sgn1]

lemma sgn_bxor_left (z w b : Bits n) : sgn (bxor z w) b = sgn z b * sgn w b := by
  simp only [sgn, bxor_apply, sgn1_xor_left]
  exact Finset.prod_mul_distrib

@[simp] lemma sgn_zero_right (z : Bits n) : sgn z (fun _ => false) = 1 := by
  simp [sgn, sgn1]

@[simp] lemma sgn_zero_left (b : Bits n) : sgn (fun _ => false) b = 1 := by
  simp [sgn, sgn1]

lemma sgn_condVec_right (z : Bits n) (c : Bool) (j : Fin n) :
    sgn z (condVec c j) = if c then sgn1 (z j) true else 1 := by
  unfold sgn
  rw [Finset.prod_eq_single j]
  · cases c <;> simp [sgn1]
  · intro i _ hij
    rw [condVec_of_ne hij]
    simp [sgn1]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma sgn_condVec_left (b : Bits n) (c : Bool) (j : Fin n) :
    sgn (condVec c j) b = if c then sgn1 (b j) true else 1 := by
  rw [show sgn (condVec c j) b = sgn b (condVec c j) by
        unfold sgn; exact Finset.prod_congr rfl fun i _ => sgn1_comm _ _]
  exact sgn_condVec_right _ _ _

lemma sgn_mul_self (z b : Bits n) : sgn z b * sgn z b = 1 := by
  rw [← sgn_bxor_right]; simp

lemma sgn_ne_zero (z b : Bits n) : sgn z b ≠ 0 := by
  intro h
  have := sgn_mul_self z b
  rw [h] at this
  simp at this

/-! ## Pauli operators -/

/-- An `n`-qubit Pauli operator, stored as a phase in `{1,i,-1,-i}` together with the
`X`-part and `Z`-part bit strings: it denotes `i^ph · X^xs · Z^zs`. -/
structure Pauli (n : ℕ) where
  /-- the power of `i` in the phase -/
  ph : Fin 4
  /-- the `X`-part -/
  xs : Bits n
  /-- the `Z`-part -/
  zs : Bits n
deriving DecidableEq

/-- The matrix of a Pauli operator in the computational basis. -/
def matP (p : Pauli n) : Matrix (Bits n) (Bits n) ℂ :=
  fun b b' => if b = bxor b' p.xs then Complex.I ^ (p.ph : ℕ) * sgn p.zs b' else 0

lemma matP_apply (p : Pauli n) (b b' : Bits n) :
    matP p b b' = if b = bxor b' p.xs then Complex.I ^ (p.ph : ℕ) * sgn p.zs b' else 0 := rfl

lemma mul_matP (M : Matrix (Bits n) (Bits n) ℂ) (p : Pauli n) (b b' : Bits n) :
    (M * matP p) b b' = M b (bxor b' p.xs) * (Complex.I ^ (p.ph : ℕ) * sgn p.zs b') := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (bxor b' p.xs)]
  · simp [matP_apply]
  · intro c _ hc
    simp [matP_apply, hc]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma matP_mul (M : Matrix (Bits n) (Bits n) ℂ) (p : Pauli n) (b b' : Bits n) :
    (matP p * M) b b' =
      (Complex.I ^ (p.ph : ℕ) * sgn p.zs (bxor b p.xs)) * M (bxor b p.xs) b' := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (bxor b p.xs)]
  · simp [matP_apply]
  · intro c _ hc
    have : ¬ (b = bxor c p.xs) := by
      intro h; exact hc (by rw [h]; simp)
    simp [matP_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Clifford gates -/

/-- The generators of the Clifford group: Hadamard, phase gate, and CNOT (on distinct wires). -/
inductive Gate (n : ℕ)
  | H : Fin n → Gate n
  | S : Fin n → Gate n
  | CX (j k : Fin n) (h : j ≠ k) : Gate n

/-- `1/√2`, the normalisation of the Hadamard gate. -/
noncomputable def invSqrt2 : ℂ := (Real.sqrt 2 : ℝ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  unfold invSqrt2
  rw [← mul_inv, h]
  norm_num

@[simp] lemma star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-- Two bit strings agreeing away from coordinate `j`. -/
def agreeOff (j : Fin n) (b c : Bits n) : Prop := ∀ i, i ≠ j → b i = c i

instance (j : Fin n) (b c : Bits n) : Decidable (agreeOff j b c) := by
  unfold agreeOff; infer_instance

/-- The action of `CNOT` with control `j` and target `k` on basis labels. -/
def cxf (j k : Fin n) (b : Bits n) : Bits n := bxor b (condVec (b j) k)

/-- The dual (`Z`-part) action of `CNOT` with control `j` and target `k`. -/
def czf (j k : Fin n) (z : Bits n) : Bits n := bxor z (condVec (z k) j)

/-- The matrix of a Clifford generator. -/
noncomputable def matGate : Gate n → Matrix (Bits n) (Bits n) ℂ
  | .H j => fun b c => if agreeOff j b c then invSqrt2 * sgn1 (b j) (c j) else 0
  | .S j => fun b c => if b = c then (if b j then Complex.I else 1) else 0
  | .CX j k _ => fun b c => if b = cxf j k c then 1 else 0

/-- The classical (tableau) update rule corresponding to a Clifford generator. -/
def stepGate : Gate n → Pauli n → Pauli n
  | .H j => fun p =>
      { ph := p.ph + (if p.xs j && p.zs j then 2 else 0)
        xs := bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j)
        zs := bxor p.zs (condVec (xor (p.xs j) (p.zs j)) j) }
  | .S j => fun p =>
      { ph := p.ph + (if p.xs j then 1 else 0)
        xs := p.xs
        zs := bxor p.zs (condVec (p.xs j) j) }
  | .CX j k _ => fun p =>
      { ph := p.ph
        xs := cxf j k p.xs
        zs := czf j k p.zs }

/-- The set of wires a gate acts on. -/
def support : Gate n → Finset (Fin n)
  | .H j => {j}
  | .S j => {j}
  | .CX j k _ => {j, k}

/-! ## Unitarity of the generators -/

lemma sum_eq_pair (j : Fin n) (f : Bits n → ℂ) (b : Bits n)
    (h0 : ∀ c, ¬ agreeOff j c b → f c = 0) :
    ∑ c, f c = f (Function.update b j false) + f (Function.update b j true) := by
  classical
  have hne : (Function.update b j false : Bits n) ≠ Function.update b j true := by
    intro h; simpa using congrFun h j
  have key : ∀ c ∈ (Finset.univ : Finset (Bits n)),
      c ∉ ({Function.update b j false, Function.update b j true} : Finset (Bits n)) →
      f c = 0 := by
    intro c _ hc
    apply h0
    intro hagree
    have hcu : c = Function.update b j (c j) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne hij]
        exact hagree i hij
    apply hc
    cases hcj : c j
    · exact Finset.mem_insert.2 (Or.inl (hcu.trans (by rw [hcj])))
    · exact Finset.mem_insert.2 (Or.inr (by
        simp only [Finset.mem_singleton]
        exact hcu.trans (by rw [hcj])))
  rw [← Finset.sum_subset (Finset.subset_univ _) key, Finset.sum_pair hne]

lemma matGate_H_apply (j : Fin n) (b c : Bits n) :
    (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) b c =
      if agreeOff j b c then invSqrt2 * sgn1 (b j) (c j) else 0 := rfl

lemma agreeOff_symm {j : Fin n} {b c : Bits n} (h : agreeOff j b c) : agreeOff j c b :=
  fun i hi => (h i hi).symm

lemma agreeOff_trans {j : Fin n} {b c d : Bits n} (h1 : agreeOff j b c) (h2 : agreeOff j c d) :
    agreeOff j b d := fun i hi => (h1 i hi).trans (h2 i hi)

lemma agreeOff_update (j : Fin n) (b : Bits n) (v : Bool) :
    agreeOff j b (Function.update b j v) := fun i hi => by rw [Function.update_of_ne hi]

lemma eq_of_agreeOff {j : Fin n} {b c : Bits n} (h : agreeOff j b c) (hj : b j = c j) : b = c := by
  funext i
  by_cases hi : i = j
  · subst hi; exact hj
  · exact h i hi

lemma star_sgn1 (a b : Bool) : star (sgn1 a b) = sgn1 a b := by
  cases a <;> cases b <;> simp [sgn1]

lemma matGate_H_star (j : Fin n) : star (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ)
    = matGate (Gate.H j) := by
  funext b c
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, matGate_H_apply]
  by_cases h : agreeOff j b c
  · rw [if_pos (agreeOff_symm h), if_pos h, star_mul', star_invSqrt2, star_sgn1, sgn1_comm]
  · rw [if_neg (fun hh => h (agreeOff_symm hh)), if_neg h, star_zero]

lemma matGate_H_mul_self (j : Fin n) :
    (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) * matGate (Gate.H j) = 1 := by
  funext b c
  rw [Matrix.mul_apply]
  rw [sum_eq_pair j _ b (fun d hd => ?_)]
  · have e1 : ∀ v : Bool, (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) b
        (Function.update b j v) = invSqrt2 * sgn1 (b j) v := by
      intro v
      rw [matGate_H_apply, if_pos (agreeOff_update j b v)]
      simp
    by_cases hbc : agreeOff j b c
    · have e2 : ∀ v : Bool, (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ)
          (Function.update b j v) c = invSqrt2 * sgn1 v (c j) := by
        intro v
        rw [matGate_H_apply,
          if_pos (agreeOff_trans (agreeOff_symm (agreeOff_update j b v)) hbc)]
        simp
      have key : ∀ u w : Bool, invSqrt2 * sgn1 u false * (invSqrt2 * sgn1 false w)
            + invSqrt2 * sgn1 u true * (invSqrt2 * sgn1 true w)
          = if u = w then 1 else 0 := by
        intro u w
        cases u <;> cases w <;> norm_num [sgn1] <;>
          first
            | linear_combination (2 : ℂ) * invSqrt2_mul_self
            | ring
      rw [e1, e1, e2, e2, key, Matrix.one_apply]
      by_cases hj : b j = c j
      · rw [if_pos hj, if_pos (eq_of_agreeOff hbc hj)]
      · rw [if_neg hj, if_neg (fun hh => hj (by rw [hh]))]
    · have e2 : ∀ v : Bool, (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ)
          (Function.update b j v) c = 0 := by
        intro v
        rw [matGate_H_apply, if_neg]
        intro hh
        exact hbc (agreeOff_trans (agreeOff_update j b v) hh)
      have hne : b ≠ c := by
        intro hh; exact hbc (fun i _ => by rw [hh])
      rw [e2, e2, Matrix.one_apply_ne hne]
      ring
  · rw [matGate_H_apply, if_neg (fun hh => hd (agreeOff_symm hh)), zero_mul]

lemma matGate_S_diagonal (j : Fin n) :
    (matGate (Gate.S j) : Matrix (Bits n) (Bits n) ℂ)
      = Matrix.diagonal (fun b => if b j then Complex.I else 1) := rfl

lemma matGate_S_unitary (j : Fin n) :
    (matGate (Gate.S j) : Matrix (Bits n) (Bits n) ℂ) ∈ unitary (Matrix (Bits n) (Bits n) ℂ) := by
  rw [Unitary.mem_iff, matGate_S_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]
  constructor <;>
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext b
      by_cases hb : b j = true <;>
        simp [hb, Pi.star_apply, Complex.conj_I, Complex.I_mul_I]

lemma cxf_apply_control (j k : Fin n) (h : j ≠ k) (b : Bits n) : cxf j k b j = b j := by
  simp [cxf, condVec, h]

lemma cxf_involutive (j k : Fin n) (h : j ≠ k) (b : Bits n) : cxf j k (cxf j k b) = b := by
  rw [cxf, cxf_apply_control j k h]
  simp [cxf]

lemma cxf_eq_iff (j k : Fin n) (h : j ≠ k) (b c : Bits n) : b = cxf j k c ↔ c = cxf j k b := by
  constructor <;> · rintro rfl; rw [cxf_involutive j k h]

lemma matGate_CX_unitary (j k : Fin n) (h : j ≠ k) :
    (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ) ∈
      unitary (Matrix (Bits n) (Bits n) ℂ) := by
  have hstar : star (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ)
      = matGate (Gate.CX j k h) := by
    funext b c
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, matGate]
    by_cases hbc : c = cxf j k b
    · rw [if_pos hbc, if_pos ((cxf_eq_iff j k h b c).2 hbc)]
      simp
    · rw [if_neg hbc, if_neg (fun hh => hbc ((cxf_eq_iff j k h b c).1 hh))]
      simp
  have hmul : (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ) * matGate (Gate.CX j k h)
      = 1 := by
    funext b c
    rw [Matrix.mul_apply, Finset.sum_eq_single (cxf j k c)]
    · simp [matGate, cxf_involutive j k h, Matrix.one_apply]
    · intro d _ hd
      simp [matGate, hd]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  rw [Unitary.mem_iff, hstar]
  exact ⟨hmul, hmul⟩

lemma matGate_unitary (g : Gate n) :
    (matGate g : Matrix (Bits n) (Bits n) ℂ) ∈ unitary (Matrix (Bits n) (Bits n) ℂ) := by
  cases g with
  | H j =>
      rw [Unitary.mem_iff]
      rw [matGate_H_star j]
      exact ⟨matGate_H_mul_self j, matGate_H_mul_self j⟩
  | S j => exact matGate_S_unitary j
  | CX j k h => exact matGate_CX_unitary j k h

/-! ## Heisenberg evolution of Pauli operators -/

lemma I_pow_fin4_add (a b : Fin 4) :
    Complex.I ^ ((a + b : Fin 4) : ℕ) = Complex.I ^ (a : ℕ) * Complex.I ^ (b : ℕ) := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.add_def, pow_succ, Complex.I_mul_I]

lemma condVec_bxor_condVec (c1 c2 : Bool) (j : Fin n) :
    bxor (condVec c1 j) (condVec c2 j) = condVec (xor c1 c2) j := by
  funext i
  by_cases hi : i = j <;> simp [condVec, hi]

lemma update_eq_bxor (u : Bits n) (j : Fin n) (v : Bool) :
    Function.update u j v = bxor u (condVec (xor (u j) v) j) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [condVec]
  · simp [Function.update_of_ne hi, condVec, hi]

lemma eq_bxor_condVec_of_agreeOff {j : Fin n} {b u : Bits n} (h : agreeOff j b u) :
    b = bxor u (condVec (xor (u j) (b j)) j) := by
  rw [← update_eq_bxor]
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · rw [Function.update_of_ne hi]; exact h i hi

lemma bool_xor_shuffle (a q r s : Bool) : xor (xor (xor a q) r) (xor q s) = xor a (xor r s) := by
  cases a <;> cases q <;> cases r <;> cases s <;> rfl

lemma bxor_shuffle (a x c1 c2 : Bits n) :
    bxor (bxor (bxor a x) c1) (bxor x c2) = bxor a (bxor c1 c2) := by
  funext i
  simp only [bxor_apply]
  exact bool_xor_shuffle (a i) (x i) (c1 i) (c2 i)

lemma intertwine_H (j : Fin n) (p : Pauli n) :
    (matGate (Gate.H j) : Matrix (Bits n) (Bits n) ℂ) * matP p
      = matP (stepGate (Gate.H j) p) * matGate (Gate.H j) := by
  funext b b'
  rw [mul_matP, matP_mul, matGate_H_apply, matGate_H_apply]
  have hstepx : (stepGate (Gate.H j) p).xs
      = bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j) := rfl
  have hstepz : (stepGate (Gate.H j) p).zs
      = bxor p.zs (condVec (xor (p.xs j) (p.zs j)) j) := rfl
  have hstepph : (stepGate (Gate.H j) p).ph
      = p.ph + (if p.xs j && p.zs j then 2 else 0) := rfl
  rw [hstepx, hstepz, hstepph]
  have hiff : agreeOff j b (bxor b' p.xs) ↔
      agreeOff j (bxor b (bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j))) b' := by
    constructor
    · intro hh i hi
      have h1 : b i = xor (b' i) (p.xs i) := hh i hi
      show xor (b i) (xor (p.xs i) (condVec (xor (p.xs j) (p.zs j)) j i)) = b' i
      rw [condVec_of_ne hi, h1]
      simp
    · intro hh i hi
      have h1 : xor (b i) (xor (p.xs i) (condVec (xor (p.xs j) (p.zs j)) j i)) = b' i := hh i hi
      rw [condVec_of_ne hi] at h1
      show b i = xor (b' i) (p.xs i)
      rw [← h1]
      simp
  by_cases hb : agreeOff j b (bxor b' p.xs)
  · rw [if_pos hb, if_pos (hiff.1 hb)]
    have hbu := eq_bxor_condVec_of_agreeOff hb
    have hkey : bxor b (bxor p.xs (condVec (xor (p.xs j) (p.zs j)) j))
        = bxor b' (condVec (xor (xor ((bxor b' p.xs) j) (b j))
            (xor (p.xs j) (p.zs j))) j) := by
      conv_lhs => rw [hbu]
      rw [bxor_shuffle, condVec_bxor_condVec]
    rw [hkey, sgn_bxor_left, sgn_bxor_right, sgn_bxor_right, sgn_condVec_right,
      sgn_condVec_left, sgn_condVec_left, condVec_self, I_pow_fin4_add]
    simp only [bxor_apply, condVec_self]
    by_cases hB : b' j = true <;> by_cases hX : p.xs j = true <;>
      by_cases hZ : p.zs j = true <;> by_cases hv : b j = true <;>
      simp [hB, hX, hZ, hv, sgn1, Complex.I_mul_I] <;> ring
  · rw [if_neg hb, zero_mul, if_neg (fun hh => hb (hiff.2 hh)), mul_zero]

lemma intertwine_S (j : Fin n) (p : Pauli n) :
    (matGate (Gate.S j) : Matrix (Bits n) (Bits n) ℂ) * matP p
      = matP (stepGate (Gate.S j) p) * matGate (Gate.S j) := by
  funext b b'
  rw [mul_matP, matP_mul]
  simp only [stepGate, matGate]
  by_cases hb : b = bxor b' p.xs
  · subst hb
    rw [if_pos rfl, if_pos (by simp : bxor (bxor b' p.xs) p.xs = b')]
    rw [I_pow_fin4_add, sgn_bxor_left, sgn_condVec_left]
    simp only [bxor_apply, bxor_cancel_right]
    by_cases hx : p.xs j = true <;> by_cases hbj : b' j = true <;>
      simp [hx, hbj, sgn1, Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_mul_I] <;> ring
  · have hb2 : ¬ (bxor b p.xs = b') := fun hh => hb (by rw [← hh]; simp)
    rw [if_neg hb, zero_mul, if_neg hb2, mul_zero]

lemma cxf_bxor (j k : Fin n) (u v : Bits n) :
    cxf j k (bxor u v) = bxor (cxf j k u) (cxf j k v) := by
  funext i
  simp only [cxf, bxor_apply, condVec_apply]
  cases hik : decide (i = k) <;> cases u j <;> cases v j <;> simp [Bool.xor_comm]

lemma sgn_czf_cxf (j k : Fin n) (h : j ≠ k) (z b : Bits n) :
    sgn (czf j k z) (cxf j k b) = sgn z b := by
  rw [czf, cxf, sgn_bxor_left, sgn_bxor_right, sgn_bxor_right, sgn_condVec_left,
    sgn_condVec_right, sgn_condVec_left]
  have hjk : (decide (j = k)) = false := by simp [h]
  simp only [condVec_apply, hjk, Bool.and_false]
  by_cases hz : z k = true <;> by_cases hbj : b j = true <;> simp [hz, hbj, sgn1]

lemma intertwine_CX (j k : Fin n) (h : j ≠ k) (p : Pauli n) :
    (matGate (Gate.CX j k h) : Matrix (Bits n) (Bits n) ℂ) * matP p
      = matP (stepGate (Gate.CX j k h) p) * matGate (Gate.CX j k h) := by
  funext b b'
  rw [mul_matP, matP_mul]
  simp only [stepGate, matGate]
  by_cases hb : b = cxf j k (bxor b' p.xs)
  · have hb2 : bxor b (cxf j k p.xs) = cxf j k b' := by
      rw [hb, cxf_bxor]
      simp
    rw [if_pos hb, if_pos hb2, one_mul, mul_one, hb2, sgn_czf_cxf j k h]
  · have hb2 : ¬ (bxor b (cxf j k p.xs) = cxf j k b') := by
      intro hh
      apply hb
      have hb3 : b = bxor (cxf j k b') (cxf j k p.xs) := by rw [← hh]; simp
      rw [hb3, cxf_bxor]
    rw [if_neg hb, if_neg hb2, zero_mul, mul_zero]

lemma intertwine (g : Gate n) (p : Pauli n) :
    (matGate g : Matrix (Bits n) (Bits n) ℂ) * matP p = matP (stepGate g p) * matGate g := by
  cases g with
  | H j => exact intertwine_H j p
  | S j => exact intertwine_S j p
  | CX j k h => exact intertwine_CX j k h p

lemma conj_gate (g : Gate n) (p : Pauli n) :
    (matGate g : Matrix (Bits n) (Bits n) ℂ) * matP p * star (matGate g)
      = matP (stepGate g p) := by
  rw [intertwine g p, Matrix.mul_assoc, (Unitary.mem_iff.1 (matGate_unitary g)).2, mul_one]

/-! ## Circuits -/

/-- The unitary implemented by a circuit; the head of the list is applied first. -/
noncomputable def circuitMat : List (Gate n) → Matrix (Bits n) (Bits n) ℂ
  | [] => 1
  | g :: C => circuitMat C * matGate g

/-- The classical simulation of a circuit acting on a Pauli operator (Heisenberg picture). -/
def simulate : List (Gate n) → Pauli n → Pauli n
  | [], p => p
  | g :: C, p => simulate C (stepGate g p)

lemma circuitMat_unitary (C : List (Gate n)) :
    (circuitMat C : Matrix (Bits n) (Bits n) ℂ) ∈ unitary (Matrix (Bits n) (Bits n) ℂ) := by
  induction C with
  | nil => simp only [circuitMat]; exact (unitary (Matrix (Bits n) (Bits n) ℂ)).one_mem
  | cons g C ih => exact (Submonoid.mul_mem _ ih (matGate_unitary g))

lemma circuit_conj (C : List (Gate n)) (p : Pauli n) :
    (circuitMat C : Matrix (Bits n) (Bits n) ℂ) * matP p * star (circuitMat C)
      = matP (simulate C p) := by
  induction C generalizing p with
  | nil => simp [circuitMat, simulate]
  | cons g C ih =>
      show circuitMat C * matGate g * matP p * star (circuitMat C * matGate g) = _
      rw [star_mul,
        show circuitMat C * matGate g * matP p * (star (matGate g) * star (circuitMat C))
            = circuitMat C * (matGate g * matP p * star (matGate g)) * star (circuitMat C) from by
          simp [Matrix.mul_assoc],
        conj_gate]
      exact ih (stepGate g p)

/-! ## Locality: each gate touches only `O(1)` bits of the tableau -/

lemma stepGate_local (g : Gate n) (p : Pauli n) (i : Fin n) (hi : i ∉ support g) :
    (stepGate g p).xs i = p.xs i ∧ (stepGate g p).zs i = p.zs i := by
  cases g with
  | H j =>
      simp only [support, Finset.mem_singleton] at hi
      constructor <;> simp [stepGate, hi]
  | S j =>
      simp only [support, Finset.mem_singleton] at hi
      constructor <;> simp [stepGate, hi]
  | CX j k h =>
      simp only [support, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      constructor <;> simp [stepGate, cxf, czf, hi.1, hi.2]

/-! ## The Gottesman–Knill theorem -/

/--
**Gottesman–Knill.**  Stabilizer (Clifford) circuits are efficiently classically simulable.

Concretely, for every circuit `C` built from the Clifford generators `H`, `S`, `CNOT` on `n`
qubits, the purely classical tableau update `simulate C : Pauli n → Pauli n`, which stores only
`2n + 2` bits per Pauli operator, reproduces the Heisenberg evolution of every Pauli operator
under the (genuinely `2^n`-dimensional, unitary) circuit matrix `circuitMat C`:

1. `circuitMat C` is unitary;
2. `circuitMat C • P • (circuitMat C)† = simulate C P` for every Pauli `P`;
3. each classical gate step alters the tableau only in the (at most two) coordinates the gate
   acts on, and leaves the rest untouched — so simulating `m` gates on a stabilizer state given
   by `n` Pauli generators costs `O(n·m)` elementary bit operations;
4. consequently stabilizers are propagated: if `P` stabilizes a state `v`, then `simulate C P`
   stabilizes the evolved state `circuitMat C v`.
-/
theorem gottesman_knill (n : ℕ) (C : List (Gate n)) :
    (circuitMat C : Matrix (Bits n) (Bits n) ℂ) ∈ unitary (Matrix (Bits n) (Bits n) ℂ) ∧
    (∀ p : Pauli n,
      circuitMat C * matP p * star (circuitMat C) = matP (simulate C p)) ∧
    (∀ (g : Gate n) (p : Pauli n) (i : Fin n), i ∉ support g →
      (stepGate g p).xs i = p.xs i ∧ (stepGate g p).zs i = p.zs i) ∧
    (∀ (p : Pauli n) (v : Bits n → ℂ), matP p *ᵥ v = v →
      matP (simulate C p) *ᵥ (circuitMat C *ᵥ v) = circuitMat C *ᵥ v) := by
  refine ⟨circuitMat_unitary C, fun p => circuit_conj C p, fun g p i hi => stepGate_local g p i hi,
    ?_⟩
  intro p v hv
  have hU := (Unitary.mem_iff.1 (circuitMat_unitary C)).1
  have h1 : star (circuitMat C) *ᵥ (circuitMat C *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [← circuit_conj C p, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, hv]

end QI

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

