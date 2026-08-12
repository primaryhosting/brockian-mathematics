/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

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
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Gottesman–Knill

We formalise the Gottesman–Knill theorem: a quantum circuit built out of Clifford gates
(Hadamard, phase, CNOT) acting on `n` qubits can be simulated classically with only
`2n + 2` bits of memory and a constant amount of work per gate, in the Heisenberg picture.

The `2^n`-dimensional Hilbert space is modelled as `Bits n → ℂ`, i.e. operators are
matrices indexed by bitstrings `Bits n = Fin n → Bool`.

A Pauli operator is stored as a *tableau row* `(k, x, z)` with `k : ZMod 4` a phase
exponent and `x z : Bits n`; it denotes the operator `i^k X^x Z^z`, whose matrix is
`|b⟩ ↦ i^k (-1)^{z·b} |b ⊕ x⟩`.

The three main ingredients are:

* `QI.gateMat_unitary` : the gate matrices are unitary;
* `QI.gate_conj` : conjugating a Pauli matrix by a Clifford gate matrix is computed
  exactly by the (purely classical, bit-level) tableau update `QI.gateConj`;
* `QI.gateConj_local` : the tableau update only touches the qubits in the gate's support.

Together these give `QI.gottesman_knill`.
-/

namespace QI

/-- Bitstrings of length `n`; these index the computational basis of `n` qubits. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- Bitwise XOR of two bitstrings. -/
def bxor {n : ℕ} (u v : Bits n) : Bits n := fun i => xor (u i) (v i)

/-- The `𝔽₂`-valued inner product of two bitstrings. -/
def bdot {n : ℕ} (u v : Bits n) : ZMod 2 := ∑ i, cond (u i && v i) 1 0

/-- `esgn a = (-1)^a` for `a : ZMod 2`. -/
def esgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

/-- `iPow k = i^k` for `k : ZMod 4`. -/
noncomputable def iPow (k : ZMod 4) : ℂ := Complex.I ^ (k.val)

/-- A row of a stabilizer tableau: the Pauli operator `i^k X^x Z^z`. This is `2n + 2`
bits of classical data. -/
@[ext]
structure Pauli (n : ℕ) where
  /-- phase exponent -/
  k : ZMod 4
  /-- `X`-part -/
  x : Bits n
  /-- `Z`-part -/
  z : Bits n

/-- The matrix of the Pauli operator `i^k X^x Z^z`, acting by `|b⟩ ↦ i^k (-1)^{z·b} |b ⊕ x⟩`. -/
noncomputable def Pauli.toMatrix {n : ℕ} (P : Pauli n) : Matrix (Bits n) (Bits n) ℂ :=
  fun a b => if a = bxor b P.x then iPow P.k * esgn (bdot P.z b) else 0

/-- The tableau row is just `2n + 2` bits of classical data. -/
def pauliEquiv (n : ℕ) : Pauli n ≃ ZMod 4 × Bits n × Bits n where
  toFun P := (P.k, P.x, P.z)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypePauli (n : ℕ) : Fintype (Pauli n) := Fintype.ofEquiv _ (pauliEquiv n).symm

/-- The classical simulator's state space has `4 · 4 ^ n` elements, i.e. `2n + 2` bits,
compared with the `2 ^ n`-dimensional quantum state space. -/
lemma card_pauli (n : ℕ) : Fintype.card (Pauli n) = 4 * 2 ^ n * 2 ^ n := by
  rw [Fintype.card_congr (pauliEquiv n)]
  simp [Fintype.card_prod, ZMod.card, mul_assoc]

/-- The Clifford generators. -/
inductive Gate (n : ℕ) where
  /-- Hadamard on qubit `j` -/
  | H : Fin n → Gate n
  /-- Phase gate `S = diag(1, i)` on qubit `j` -/
  | S : Fin n → Gate n
  /-- `CNOT` with control `c` and target `t` -/
  | CX : (c t : Fin n) → c ≠ t → Gate n

/-- The bit-flip of the target `t` controlled by `c`, i.e. the classical action of `CNOT`
on a computational basis state. -/
def flipT {n : ℕ} (c t : Fin n) (b : Bits n) : Bits n := Function.update b t (xor (b t) (b c))

/-- The unitary matrix implementing a Clifford generator. -/
noncomputable def gateMat {n : ℕ} : Gate n → Matrix (Bits n) (Bits n) ℂ
  | .H j => fun a b =>
      if (∀ i, i ≠ j → a i = b i) then
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if a j && b j then -1 else 1)
      else 0
  | .S j => fun a b => if a = b then (if a j then Complex.I else 1) else 0
  | .CX c t _ => fun a b => if a = flipT c t b then 1 else 0

/-- The classical tableau update: the Heisenberg action of a Clifford generator on a
Pauli operator, computed on the `2n+2` bits of the tableau row. -/
def gateConj {n : ℕ} : Gate n → Pauli n → Pauli n
  | .H j, P =>
      { k := P.k + (if P.x j && P.z j then 2 else 0)
        x := Function.update P.x j (P.z j)
        z := Function.update P.z j (P.x j) }
  | .S j, P =>
      { k := P.k + (if P.x j then 3 else 0)
        x := P.x
        z := Function.update P.z j (xor (P.z j) (P.x j)) }
  | .CX c t _, P =>
      { k := P.k
        x := Function.update P.x t (xor (P.x t) (P.x c))
        z := Function.update P.z c (xor (P.z c) (P.z t)) }

/-- The qubits a gate acts on. -/
def Gate.support {n : ℕ} : Gate n → Finset (Fin n)
  | .H j => {j}
  | .S j => {j}
  | .CX c t _ => {c, t}

/-- A stabilizer (Clifford) circuit: a list of Clifford generators, applied left to right. -/
abbrev Circuit (n : ℕ) : Type := List (Gate n)

/-- The unitary implemented by a circuit (the head of the list is applied first). -/
noncomputable def circuitMat {n : ℕ} : Circuit n → Matrix (Bits n) (Bits n) ℂ
  | [] => 1
  | g :: rest => circuitMat rest * gateMat g

/-- The classical simulation of a circuit: fold the tableau update over the gates. -/
def circuitConj {n : ℕ} : Circuit n → Pauli n → Pauli n
  | [], P => P
  | g :: rest, P => gateConj g (circuitConj rest P)

/-- The all-zero bitstring, i.e. the computational basis state `|0…0⟩`. -/
def zeroBits (n : ℕ) : Bits n := fun _ => false

/-! ### Basic arithmetic lemmas -/

lemma esgn_add (a b : ZMod 2) : esgn (a + b) = esgn a * esgn b := by
  fin_cases a <;> fin_cases b <;> simp only [esgn] <;> (norm_num; try decide)

lemma iPow_add (a b : ZMod 4) : iPow (a + b) = iPow a * iPow b := by
  fin_cases a <;> fin_cases b <;>
    simp only [iPow, ZMod.val_add] <;>
    norm_num [ZMod.val, Complex.ext_iff, pow_succ, Complex.I_mul_I]

lemma bxor_bxor_cancel {n : ℕ} (u v : Bits n) : bxor (bxor u v) v = u := by
  funext i; simp [bxor]

lemma bxor_eq_iff {n : ℕ} (a b v : Bits n) : a = bxor b v ↔ b = bxor a v := by
  constructor <;> rintro rfl <;> rw [bxor_bxor_cancel]

/-- The part of the `𝔽₂` inner product away from qubit `j`. -/
def bdotOff {n : ℕ} (j : Fin n) (u v : Bits n) : ZMod 2 :=
  ∑ i ∈ Finset.univ.erase j, cond (u i && v i) 1 0

lemma bdot_eq_off {n : ℕ} (j : Fin n) (u v : Bits n) :
    bdot u v = cond (u j && v j) 1 0 + bdotOff j u v := by
  rw [bdot, bdotOff, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]

lemma bdotOff_congr {n : ℕ} (j : Fin n) {u u' v v' : Bits n}
    (hu : ∀ i, i ≠ j → u i = u' i) (hv : ∀ i, i ≠ j → v i = v' i) :
    bdotOff j u v = bdotOff j u' v' := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  rw [hu i hij, hv i hij]

lemma bdot_update_j {n : ℕ} (j : Fin n) (u v : Bits n) (w : Bool) :
    bdot (Function.update u j w) v = cond (w && v j) 1 0 + bdotOff j u v := by
  rw [bdot_eq_off j, Function.update_self,
    bdotOff_congr j (fun i hi => Function.update_of_ne hi _ _) (fun _ _ => rfl)]

/-- The part of the `𝔽₂` inner product away from qubits `c` and `t`. -/
def bdotOff2 {n : ℕ} (c t : Fin n) (u v : Bits n) : ZMod 2 :=
  ∑ i ∈ (Finset.univ.erase c).erase t, cond (u i && v i) 1 0

lemma bdot_eq_off2 {n : ℕ} {c t : Fin n} (h : c ≠ t) (u v : Bits n) :
    bdot u v = cond (u c && v c) 1 0 + cond (u t && v t) 1 0 + bdotOff2 c t u v := by
  rw [bdot, bdotOff2, ← Finset.add_sum_erase _ _ (Finset.mem_univ c),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ t⟩), add_assoc]

lemma bdotOff2_congr {n : ℕ} (c t : Fin n) {u u' v v' : Bits n}
    (hu : ∀ i, i ≠ c → i ≠ t → u i = u' i) (hv : ∀ i, i ≠ c → i ≠ t → v i = v' i) :
    bdotOff2 c t u v = bdotOff2 c t u' v' := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  have h1 : i ≠ t := (Finset.mem_erase.mp hi).1
  have h2 : i ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  rw [hu i h2 h1, hv i h2 h1]

lemma iPow_zero : iPow 0 = 1 := by simp [iPow]

lemma iPow_two : iPow 2 = -1 := by
  simp only [iPow]; norm_num [ZMod.val, Complex.ext_iff, pow_succ, Complex.I_mul_I]

lemma iPow_three : iPow 3 = -Complex.I := by
  simp only [iPow]; norm_num [ZMod.val, Complex.ext_iff, pow_succ, Complex.I_mul_I]

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- The scalar identity behind the phase-gate tableau rule. -/
lemma S_scalar (k : ZMod 4) (p z beta : Bool) (R : ZMod 2) :
    iPow k * esgn (cond (z && beta) 1 0 + R) * (if beta then Complex.I else 1)
      = (if xor beta p then Complex.I else 1) *
        (iPow (k + (if p then 3 else 0)) * esgn (cond ((xor z p) && beta) 1 0 + R)) := by
  cases p <;> cases z <;> cases beta <;> fin_cases R <;>
    simp [esgn, iPow_add, iPow_three, zmod2_one_add_one] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- The scalar identity behind the Hadamard tableau rule. -/
lemma H_scalar (k : ZMod 4) (alpha beta p z : Bool) (R : ZMod 2) (s : ℂ) :
    iPow k * esgn (cond (z && (xor alpha p)) 1 0 + R) *
        (s * (if (xor alpha p) && beta then -1 else 1))
      = (s * (if alpha && (xor beta z) then -1 else 1)) *
        (iPow (k + (if p && z then 2 else 0)) * esgn (cond (p && beta) 1 0 + R)) := by
  cases alpha <;> cases beta <;> cases p <;> cases z <;> fin_cases R <;>
    simp [esgn, iPow_add, iPow_two, zmod2_one_add_one] <;> ring

lemma agree_update {n : ℕ} (j : Fin n) (a c : Bits n) (h : ∀ i, i ≠ j → c i = a i) :
    c = Function.update a j (c j) := by
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · rw [Function.update_of_ne hij, h i hij]

/-- A function on bitstrings supported on the bitstrings agreeing with `a` off `j` has a
two-term sum. -/
lemma sum_pair_support {n : ℕ} (j : Fin n) (a : Bits n) (f : Bits n → ℂ)
    (hf : ∀ c, ¬(∀ i, i ≠ j → c i = a i) → f c = 0) :
    ∑ c, f c = f (Function.update a j false) + f (Function.update a j true) := by
  have hne : Function.update a j false ≠ Function.update a j true := by
    intro h
    have := congrFun h j
    rw [Function.update_self, Function.update_self] at this
    exact Bool.noConfusion this
  rw [← Finset.sum_subset (Finset.subset_univ ({Function.update a j false,
    Function.update a j true} : Finset (Bits n)))]
  · rw [Finset.sum_pair hne]
  · intro c _ hc
    apply hf
    intro hagree
    have h1 := agree_update j a c hagree
    cases hcj : c j with
    | false =>
        have h2 : c = Function.update a j false := by rw [h1, hcj]
        exact hc (h2 ▸ Finset.mem_insert_self _ _)
    | true =>
        have h2 : c = Function.update a j true := by rw [h1, hcj]
        exact hc (h2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma flipT_ne {n : ℕ} (c t : Fin n) (b : Bits n) {i : Fin n} (hi : i ≠ t) :
    flipT c t b i = b i := Function.update_of_ne hi _ _

lemma flipT_at {n : ℕ} (c t : Fin n) (b : Bits n) :
    flipT c t b t = xor (b t) (b c) := Function.update_self _ _ _

lemma flipT_involutive {n : ℕ} {c t : Fin n} (h : c ≠ t) (b : Bits n) :
    flipT c t (flipT c t b) = b := by
  funext i
  by_cases hi : i = t
  · subst hi
    rw [flipT_at, flipT_at, flipT_ne c i b h]
    cases b i <;> cases b c <;> simp
  · rw [flipT_ne c t _ hi, flipT_ne c t _ hi]

lemma flipT_inj {n : ℕ} {c t : Fin n} (h : c ≠ t) {a b : Bits n}
    (hab : flipT c t a = flipT c t b) : a = b := by
  have := congrArg (flipT c t) hab
  rwa [flipT_involutive h, flipT_involutive h] at this

/-! ### Gate matrix entries -/

lemma gateMat_H_apply {n : ℕ} (j : Fin n) (a b : Bits n) :
    gateMat (Gate.H j) a b =
      if (∀ i, i ≠ j → a i = b i) then
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if a j && b j then -1 else 1)
      else 0 := rfl

lemma gateMat_S_apply {n : ℕ} (j : Fin n) (a b : Bits n) :
    gateMat (Gate.S j) a b = if a = b then (if a j then Complex.I else 1) else 0 := rfl

lemma gateMat_CX_apply {n : ℕ} {c t : Fin n} (h : c ≠ t) (a b : Bits n) :
    gateMat (Gate.CX c t h) a b = if a = flipT c t b then 1 else 0 := rfl

/-! ### Monomial multiplication -/

lemma toMatrix_mul_apply {n : ℕ} (P : Pauli n) (M : Matrix (Bits n) (Bits n) ℂ)
    (a b : Bits n) :
    (P.toMatrix * M) a b = iPow P.k * esgn (bdot P.z (bxor a P.x)) * M (bxor a P.x) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (bxor a P.x)]
  · simp [Pauli.toMatrix, bxor_bxor_cancel]
  · intro c _ hc
    have h : a ≠ bxor c P.x := fun h => hc (by rw [h, bxor_bxor_cancel])
    simp [Pauli.toMatrix, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mul_toMatrix_apply {n : ℕ} (M : Matrix (Bits n) (Bits n) ℂ) (P : Pauli n)
    (a b : Bits n) :
    (M * P.toMatrix) a b = M a (bxor b P.x) * (iPow P.k * esgn (bdot P.z b)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (bxor b P.x)]
  · simp [Pauli.toMatrix]
  · intro c _ hc
    simp [Pauli.toMatrix, hc]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Unitarity of the gates -/

lemma gateMat_unitary {n : ℕ} (g : Gate n) : (gateMat g)ᴴ * gateMat g = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  cases g with
  | H j =>
      have hf : ∀ c : Bits n, ¬(∀ i, i ≠ j → c i = a i) →
          (starRingEnd ℂ) (gateMat (Gate.H j) c a) * gateMat (Gate.H j) c b = 0 := by
        intro c hc
        have h0 : gateMat (Gate.H j) c a = 0 := by rw [gateMat_H_apply, if_neg hc]
        rw [h0]; simp
      rw [sum_pair_support j a _ hf]
      by_cases hab : ∀ i, i ≠ j → a i = b i
      · have hupda : ∀ v : Bool, (∀ i, i ≠ j → (Function.update a j v) i = a i) := by
          intro v i hi; rw [Function.update_of_ne hi]
        have hupdb : ∀ v : Bool, (∀ i, i ≠ j → (Function.update a j v) i = b i) := by
          intro v i hi; rw [Function.update_of_ne hi]; exact hab i hi
        simp only [gateMat_H_apply, if_pos (hupda false), if_pos (hupda true),
          if_pos (hupdb false), if_pos (hupdb true), Function.update_self]
        have hone : (1 : Matrix (Bits n) (Bits n) ℂ) a b = if a j = b j then 1 else 0 := by
          rw [Matrix.one_apply]
          by_cases h : a j = b j
          · rw [if_pos h, if_pos]
            funext i
            by_cases hi : i = j
            · subst hi; exact h
            · exact hab i hi
          · rw [if_neg h, if_neg]
            intro hh; exact h (congrFun hh j)
        rw [hone]
        cases hja : a j <;> cases hjb : b j <;>
          simp only [Bool.and_false, Bool.and_true, if_true, map_mul, map_one, map_neg,
            Complex.conj_ofReal, ← Complex.ofReal_inv] <;>
          simp [sqrt2_inv_sq] <;> norm_num
      · have hane : a ≠ b := fun h => hab (fun i _ => by rw [h])
        have hnb : ∀ v : Bool, ¬ (∀ i, i ≠ j → (Function.update a j v) i = b i) := by
          intro v h; exact hab (fun i hi => by rw [← h i hi, Function.update_of_ne hi])
        simp only [gateMat_H_apply]
        rw [if_neg (hnb false), if_neg (hnb true), Matrix.one_apply_ne hane]
        ring
  | S j =>
      rw [Finset.sum_eq_single a]
      · by_cases hab : a = b
        · subst hab
          simp only [gateMat_S_apply, Matrix.one_apply_eq]
          cases h : a j <;> simp [Complex.conj_I, Complex.I_mul_I]
        · simp only [gateMat_S_apply, if_neg hab, mul_zero]
          rw [Matrix.one_apply_ne hab]
      · intro d _ hd
        simp only [gateMat_S_apply, if_neg hd, map_zero, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh
  | CX c t h =>
      rw [Finset.sum_eq_single (flipT c t a)]
      · simp only [gateMat_CX_apply, if_true, map_one, one_mul]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl, Matrix.one_apply_eq]
        · rw [if_neg (fun hh => hab (flipT_inj h hh)), Matrix.one_apply_ne hab]
      · intro d _ hd
        simp only [gateMat_CX_apply, if_neg hd, map_zero, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh

/-! ### Correctness of the tableau update -/

/-- The `𝔽₂` inner product identity behind the `CNOT` tableau rule. -/
lemma CX_bdot {n : ℕ} {c t : Fin n} (h : c ≠ t) (z b : Bits n) :
    bdot z (flipT c t b) = bdot (Function.update z c (xor (z c) (z t))) b := by
  have hoff1 : bdotOff2 c t z (flipT c t b) = bdotOff2 c t z b :=
    bdotOff2_congr c t (fun _ _ _ => rfl) (fun i _ hi => flipT_ne c t b hi)
  have hoff2 : bdotOff2 c t (Function.update z c (xor (z c) (z t))) b = bdotOff2 c t z b :=
    bdotOff2_congr c t (fun i hc _ => Function.update_of_ne hc _ _) (fun _ _ _ => rfl)
  rw [bdot_eq_off2 h z (flipT c t b), bdot_eq_off2 h _ b, hoff1, hoff2,
    flipT_ne c t b h, flipT_at c t b, Function.update_self, Function.update_of_ne (Ne.symm h)]
  have key : ∀ p q r s : Bool, (cond (p && r) (1 : ZMod 2) 0) + cond (q && (xor s r)) 1 0
      = cond ((xor p q) && r) 1 0 + cond (q && s) 1 0 := by decide
  rw [key]

/-- The `X`-part identity behind the `CNOT` tableau rule. -/
lemma CX_x {n : ℕ} {c t : Fin n} (hct : c ≠ t) (b x : Bits n) :
    bxor (flipT c t b) x = flipT c t (bxor b (Function.update x t (xor (x t) (x c)))) := by
  funext i
  rcases eq_or_ne i t with hi | hi
  · rw [hi]
    show xor (flipT c t b t) (x t)
        = flipT c t (bxor b (Function.update x t (xor (x t) (x c)))) t
    rw [flipT_at, flipT_at]
    show xor (xor (b t) (b c)) (x t)
        = xor (xor (b t) (Function.update x t (xor (x t) (x c)) t))
              (xor (b c) (Function.update x t (xor (x t) (x c)) c))
    rw [Function.update_self, Function.update_of_ne hct]
    cases b t <;> cases b c <;> cases x t <;> cases x c <;> simp
  · show xor (flipT c t b i) (x i)
        = flipT c t (bxor b (Function.update x t (xor (x t) (x c)))) i
    rw [flipT_ne c t b hi, flipT_ne c t _ hi]
    show xor (b i) (x i) = xor (b i) (Function.update x t (xor (x t) (x c)) i)
    rw [Function.update_of_ne hi]

lemma gate_comm {n : ℕ} (g : Gate n) (P : Pauli n) :
    P.toMatrix * gateMat g = gateMat g * (gateConj g P).toMatrix := by
  cases g with
  | S j =>
      ext a b
      simp only [gateConj]
      rw [toMatrix_mul_apply, mul_toMatrix_apply, gateMat_S_apply, gateMat_S_apply]
      by_cases h : bxor a P.x = b
      · have ha : a = bxor b P.x := by rw [← h, bxor_bxor_cancel]
        subst ha
        rw [bxor_bxor_cancel, if_pos rfl, if_pos rfl, bdot_eq_off j P.z b, bdot_update_j]
        exact S_scalar P.k (P.x j) (P.z j) (b j) (bdotOff j P.z b)
      · have h2 : ¬ (a = bxor b P.x) := fun hh => h (by rw [hh, bxor_bxor_cancel])
        rw [if_neg h, if_neg h2, mul_zero, zero_mul]
  | H j =>
      ext a b
      simp only [gateConj]
      rw [toMatrix_mul_apply, mul_toMatrix_apply, gateMat_H_apply, gateMat_H_apply]
      have hupd : ∀ i, i ≠ j →
          (bxor b (Function.update P.x j (P.z j))) i = xor (b i) (P.x i) := by
        intro i hi
        show xor (b i) (Function.update P.x j (P.z j) i) = xor (b i) (P.x i)
        rw [Function.update_of_ne hi]
      by_cases h : ∀ i, i ≠ j → (bxor a P.x) i = b i
      · have h2 : ∀ i, i ≠ j → a i = (bxor b (Function.update P.x j (P.z j))) i := by
          intro i hi
          rw [hupd i hi]
          have hb := h i hi
          show a i = xor (b i) (P.x i)
          have bl : ∀ u v w : Bool, xor u v = w → u = xor w v := by decide
          exact bl _ _ _ hb
        rw [if_pos h, if_pos h2, bdot_eq_off j P.z (bxor a P.x),
          bdotOff_congr j (u' := P.z) (v' := b) (fun _ _ => rfl) h,
          bdot_update_j j P.z b (P.x j),
          show (bxor b (Function.update P.x j (P.z j))) j = xor (b j) (P.z j) by
            show xor (b j) (Function.update P.x j (P.z j) j) = xor (b j) (P.z j)
            rw [Function.update_self]]
        exact H_scalar P.k (a j) (b j) (P.x j) (P.z j) (bdotOff j P.z b) _
      · have h2 : ¬ (∀ i, i ≠ j → a i = (bxor b (Function.update P.x j (P.z j))) i) := by
          intro hh
          apply h
          intro i hi
          have hb := hh i hi
          rw [hupd i hi] at hb
          show xor (a i) (P.x i) = b i
          have bl : ∀ u v w : Bool, u = xor w v → xor u v = w := by decide
          exact bl _ _ _ hb
        rw [if_neg h, if_neg h2, mul_zero, zero_mul]
  | CX c t hct =>
      ext a b
      simp only [gateConj]
      rw [toMatrix_mul_apply, mul_toMatrix_apply, gateMat_CX_apply, gateMat_CX_apply]
      have key := CX_x hct b P.x
      by_cases h : bxor a P.x = flipT c t b
      · have ha : a = flipT c t (bxor b (Function.update P.x t (xor (P.x t) (P.x c)))) := by
          rw [← key, ← h, bxor_bxor_cancel]
        rw [if_pos h, if_pos ha, one_mul, mul_one, h, CX_bdot hct P.z b]
      · have h2 : ¬ (a = flipT c t (bxor b (Function.update P.x t (xor (P.x t) (P.x c))))) := by
          intro hh
          apply h
          rw [hh, ← key, bxor_bxor_cancel]
        rw [if_neg h, if_neg h2, mul_zero, zero_mul]

lemma gate_conj {n : ℕ} (g : Gate n) (P : Pauli n) :
    (gateMat g)ᴴ * P.toMatrix * gateMat g = (gateConj g P).toMatrix := by
  rw [Matrix.mul_assoc, gate_comm, ← Matrix.mul_assoc, gateMat_unitary, Matrix.one_mul]

/-- The tableau update is *local*: it only modifies the qubits in the gate's support. -/
lemma gateConj_local {n : ℕ} (g : Gate n) (P : Pauli n) (i : Fin n) (hi : i ∉ g.support) :
    (gateConj g P).x i = P.x i ∧ (gateConj g P).z i = P.z i := by
  cases g with
  | H j =>
      simp only [Gate.support, Finset.mem_singleton] at hi
      exact ⟨Function.update_of_ne hi _ _, Function.update_of_ne hi _ _⟩
  | S j =>
      simp only [Gate.support, Finset.mem_singleton] at hi
      exact ⟨rfl, Function.update_of_ne hi _ _⟩
  | CX c t h =>
      simp only [Gate.support, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact ⟨Function.update_of_ne hi.2 _ _, Function.update_of_ne hi.1 _ _⟩

lemma support_card_le_two {n : ℕ} (g : Gate n) : g.support.card ≤ 2 := by
  cases g with
  | H j => simp [Gate.support]
  | S j => simp [Gate.support]
  | CX c t h => exact le_trans (Finset.card_insert_le _ _) (by simp)

/-! ### Circuits -/

lemma circuitMat_unitary {n : ℕ} (C : Circuit n) : (circuitMat C)ᴴ * circuitMat C = 1 := by
  induction C with
  | nil => simp [circuitMat]
  | cons g rest ih =>
      simp only [circuitMat, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (circuitMat rest)ᴴ, ih, Matrix.one_mul,
        gateMat_unitary]

lemma circuit_conj {n : ℕ} (C : Circuit n) (P : Pauli n) :
    (circuitMat C)ᴴ * P.toMatrix * circuitMat C = (circuitConj C P).toMatrix := by
  induction C with
  | nil => simp [circuitMat, circuitConj]
  | cons g rest ih =>
      simp only [circuitMat, circuitConj, Matrix.conjTranspose_mul]
      rw [show (gateMat g)ᴴ * (circuitMat rest)ᴴ * P.toMatrix * (circuitMat rest * gateMat g)
            = (gateMat g)ᴴ * ((circuitMat rest)ᴴ * P.toMatrix * circuitMat rest) * gateMat g by
          simp only [Matrix.mul_assoc], ih, gate_conj]

/-- The expectation value of a Pauli observable in the state `U(C)|0…0⟩` is read off
directly from the simulated tableau row. -/
lemma toMatrix_zero_zero {n : ℕ} (Q : Pauli n) :
    Q.toMatrix (zeroBits n) (zeroBits n) = if Q.x = zeroBits n then iPow Q.k else 0 := by
  have h1 : bxor (zeroBits n) Q.x = Q.x := by funext i; simp [bxor, zeroBits]
  have hz : bdot Q.z (zeroBits n) = 0 := by simp [bdot, zeroBits]
  show (if zeroBits n = bxor (zeroBits n) Q.x then iPow Q.k * esgn (bdot Q.z (zeroBits n)) else 0)
      = _
  rw [h1, hz]
  simp [esgn, eq_comm]

lemma expectation_eq {n : ℕ} (C : Circuit n) (P : Pauli n) :
    ((circuitMat C)ᴴ * P.toMatrix * circuitMat C) (zeroBits n) (zeroBits n)
      = if (circuitConj C P).x = zeroBits n then iPow (circuitConj C P).k else 0 := by
  rw [circuit_conj, toMatrix_zero_zero]

/-! ### The Gottesman–Knill theorem -/

/-- **Gottesman–Knill.** Stabilizer (Clifford) circuits are efficiently classically
simulable.

For `n` qubits the quantum state space has dimension `2 ^ n`, but the classical simulator
keeps only a tableau row `Pauli n`, a state space of size `4 · 4 ^ n`, i.e. `2n + 2` bits.

1. `circuitMat C` is unitary, so a circuit is a genuine quantum evolution.
2. The Heisenberg evolution `U(C)† P U(C)` of any Pauli observable `P` is computed exactly
   by the purely classical tableau fold `circuitConj C`.
3. Each gate's update is *local*: it touches only the (at most two) qubits in the gate's
   support, so simulating a circuit of `m` gates costs `O(m)` bit operations on top of
   the `O(n)` sized tableau.
4. Consequently the expectation value `⟨0…0| U(C)† P U(C) |0…0⟩` — which determines the
   statistics of any Pauli measurement on the output state — is read off from the
   simulated tableau in `O(n)` time. -/
theorem gottesman_knill (n : ℕ) :
    Fintype.card (Bits n) = 2 ^ n ∧
    Fintype.card (Pauli n) = 4 * 2 ^ n * 2 ^ n ∧
    (∀ C : Circuit n, (circuitMat C)ᴴ * circuitMat C = 1) ∧
    (∀ (C : Circuit n) (P : Pauli n),
      (circuitMat C)ᴴ * P.toMatrix * circuitMat C = (circuitConj C P).toMatrix) ∧
    (∀ (g : Gate n) (P : Pauli n) (i : Fin n), i ∉ g.support →
      (gateConj g P).x i = P.x i ∧ (gateConj g P).z i = P.z i) ∧
    (∀ g : Gate n, g.support.card ≤ 2) ∧
    (∀ (C : Circuit n) (P : Pauli n),
      ((circuitMat C)ᴴ * P.toMatrix * circuitMat C) (zeroBits n) (zeroBits n)
        = if (circuitConj C P).x = zeroBits n then iPow (circuitConj C P).k else 0) := by
  refine ⟨?_, card_pauli n, circuitMat_unitary, circuit_conj, gateConj_local,
    support_card_le_two, expectation_eq⟩
  simp

/-! ### Sanity checks: the tableau rules are the textbook Clifford conjugation rules -/

/-- `H† X H = Z`. -/
example : gateConj (Gate.H (0 : Fin 1)) ⟨0, fun _ => true, fun _ => false⟩
    = (⟨0, fun _ => false, fun _ => true⟩ : Pauli 1) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- `S† X S = -Y = i³ X Z`. -/
example : gateConj (Gate.S (0 : Fin 1)) ⟨0, fun _ => true, fun _ => false⟩
    = (⟨3, fun _ => true, fun _ => true⟩ : Pauli 1) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- `CNOT† X_c CNOT = X_c X_t`. -/
example : gateConj (Gate.CX (0 : Fin 2) 1 (by decide)) ⟨0, ![true, false], ![false, false]⟩
    = (⟨0, ![true, true], ![false, false]⟩ : Pauli 2) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- `CNOT† Z_t CNOT = Z_c Z_t`. -/
example : gateConj (Gate.CX (0 : Fin 2) 1 (by decide)) ⟨0, ![false, false], ![false, true]⟩
    = (⟨0, ![false, false], ![true, true]⟩ : Pauli 2) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- The simulator is a genuinely executable classical algorithm: here `X₀` is propagated
through the two-qubit circuit `H₀ · CNOT₀₁`, giving the stabilizer `Z₀ X₁` (phase `i⁰`). -/
example :
    ((circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).k,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).x 0,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).x 1,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).z 0,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).z 1)
      = (0, false, true, true, false) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;>
    simp [circuitConj, gateConj]

end QI

