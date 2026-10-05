import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/
def flipAt (i : Fin 9) (b : Q) : Q := fun k => if k = i then !b k else b k

lemma flipAt_invol (i : Fin 9) (b : Q) : flipAt i (flipAt i b) = b := by
  funext k; simp only [flipAt]; split <;> simp

lemma flipAt_self (i : Fin 9) (b : Q) : flipAt i b i = !b i := by
  simp [flipAt]

/-! ## Building operators -/

/-- A "monomial" operator on functions: `v ↦ (b ↦ co b * v (g b))`. -/
def piOp (co : Q → ℂ) (g : Q → Q) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) where
  toFun v := fun b => co b * v (g b)
  map_add' u v := by funext b; simp [mul_add]
  map_smul' a v := by funext b; simp [Pi.smul_apply]; ring

/-- The same operator, transported to `H`. -/
noncomputable def mkOp (co : Q → ℂ) (g : Q → Q) : H →ₗ[ℂ] H :=
  (WithLp.linearEquiv 2 ℂ (Q → ℂ)).symm.toLinearMap ∘ₗ (piOp co g) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Q → ℂ)).toLinearMap

lemma mkOp_apply (co : Q → ℂ) (g : Q → Q) (v : H) (b : Q) :
    (mkOp co g v).ofLp b = co b * v.ofLp (g b) := rfl

/-- Computational basis vector. -/
noncomputable def eb (b : Q) : H := EuclideanSpace.single b (1 : ℂ)

lemma inner_eb (a b : Q) : inner ℂ (eb a) (eb b) = if a = b then 1 else 0 := by
  simp [eb, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

lemma mkOp_eb (co : Q → ℂ) (g : Q → Q) (hg : ∀ b, g (g b) = b) (c : Q) :
    mkOp co g (eb c) = co (g c) • eb (g c) := by
  ext b
  rw [eb, mkOp_apply]
  simp only [eb, EuclideanSpace.single_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : b = g c
  · subst h; rw [hg]; simp
  · have : g b ≠ c := by intro hh; exact h (by rw [← hh, hg])
    simp [this, h]

/-! ## Single-qubit Pauli operators -/

/-- Names of the four single-qubit Pauli matrices. -/
inductive P1 | I | X | Y | Z
  deriving DecidableEq

open P1

/-- Basis-label permutation implemented by a Pauli. -/
def flP : P1 → Fin 9 → Q → Q
  | I, _, b => b
  | X, i, b => flipAt i b
  | Y, i, b => flipAt i b
  | Z, _, b => b

lemma flP_invol (p : P1) (i : Fin 9) (b : Q) : flP p i (flP p i b) = b := by
  cases p <;> simp [flP, flipAt_invol]

/-- Diagonal coefficient function of a Pauli. -/
def coP : P1 → Fin 9 → Q → ℂ
  | I, _, _ => 1
  | X, _, _ => 1
  | Y, i, b => if b i then Complex.I else -Complex.I
  | Z, i, b => if b i then -1 else 1

/-- The Pauli operator `p` acting on qubit `i`. -/
noncomputable def op (p : P1) (i : Fin 9) : H →ₗ[ℂ] H := mkOp (coP p i) (flP p i)

lemma op_I (i : Fin 9) (v : H) : op I i v = v := by
  ext b; rw [op, mkOp_apply]; simp [coP, flP]

/-- Amplitude picked up when a Pauli acts on a computational basis vector. -/
def ampP : P1 → Fin 9 → Q → ℂ
  | I, _, _ => 1
  | X, _, _ => 1
  | Y, i, b => if b i then -Complex.I else Complex.I
  | Z, i, b => if b i then -1 else 1

lemma op_eb (p : P1) (i : Fin 9) (c : Q) :
    op p i (eb c) = ampP p i c • eb (flP p i c) := by
  rw [op, mkOp_eb _ _ (flP_invol p i)]
  congr 1
  cases p <;> simp [coP, ampP, flP, flipAt_self] <;> cases c i <;> simp

/-! ## The Shor codewords -/

/-- Index type for the eight basis states in the support of the codewords. -/
abbrev T := Bool × Bool × Bool

/-- The block a qubit belongs to. -/
def blk (k : Fin 9) : Fin 3 := ⟨k.val / 3, by omega⟩

def blkVal (t : T) : Fin 3 → Bool := ![t.1, t.2.1, t.2.2]

/-- `emb t` is the basis label whose three blocks of three qubits are constant,
equal to `t.1`, `t.2.1`, `t.2.2` respectively. -/
def emb (t : T) : Q := fun k => blkVal t (blk k)

lemma emb_inj (t t' : T) : emb t = emb t' ↔ t = t' := by decide +revert

lemma flip_emb_ne (i : Fin 9) (t t' : T) : flipAt i (emb t) ≠ emb t' := by decide +revert

set_option maxRecDepth 20000 in
lemma flip_emb_eq (i j : Fin 9) (t t' : T) :
    flipAt i (emb t) = flipAt j (emb t') ↔ (i = j ∧ t = t') := by decide +revert

/-- Parity of a triple of bits. -/
def par (t : T) : Bool := xor (xor t.1 t.2.1) t.2.2

/-- Sign of the basis state `emb t` in the logical codeword `k`. -/
def sgnc (k : Bool) (t : T) : ℂ := if k && par t then -1 else 1

lemma sgnc_conj (k : Bool) (t : T) : conj (sgnc k t) = sgnc k t := by
  simp only [sgnc]; split <;> simp

lemma sgnc_sq (k : Bool) (t : T) : sgnc k t * sgnc k t = 1 := by
  simp only [sgnc]; split <;> norm_num

lemma sgnc_false (t : T) : sgnc false t = 1 := by simp [sgnc]

/-- Normalisation constant `1/√8`. -/
noncomputable def nrm : ℂ := ((Real.sqrt 8)⁻¹ : ℝ)

lemma nrm_sq : conj nrm * nrm = (1 / 8 : ℂ) := by
  have h : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  rw [nrm, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, h]
  norm_num

/-- The Shor logical codewords: `cw false = |0_L⟩`, `cw true = |1_L⟩`. -/
noncomputable def cw (k : Bool) : H := nrm • ∑ t : T, sgnc k t • eb (emb t)

lemma op_cw (p : P1) (i : Fin 9) (k : Bool) :
    op p i (cw k) = nrm • ∑ t : T, (sgnc k t * ampP p i (emb t)) • eb (flP p i (emb t)) := by
  rw [cw, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [map_smul, op_eb, smul_smul]


/-! ## When two Pauli-shifted basis states coincide -/

/-- Whether a Pauli permutes computational basis labels. -/
def flips : P1 → Bool
  | I => false
  | X => true
  | Y => true
  | Z => false

/-- Compatibility: the two Paulis have matching flip behaviour (and act on the
same qubit when they flip). -/
def compat (p q : P1) (i j : Fin 9) : Bool := (flips p == flips q) && (!flips p || (i == j))

lemma flip_emb_ne' (i : Fin 9) (t t' : T) : emb t ≠ flipAt i (emb t') :=
  fun h => flip_emb_ne i t' t h.symm

lemma flP_emb_eq_iff (p q : P1) (i j : Fin 9) (t t' : T) :
    (flP p i (emb t) = flP q j (emb t')) ↔ (compat p q i j = true ∧ t = t') := by
  cases p <;> cases q <;>
    simp [flP, compat, flips, emb_inj, flip_emb_ne, flip_emb_ne', flip_emb_eq]

/-! ## The character sums -/

def sgnZ (t : T) : ℤ := if par t then -1 else 1

def chiZ (i : Fin 9) (t : T) : ℤ := if emb t i then -1 else 1

/-- `chi i t = (-1)^(bit i of emb t)`. -/
def chi (i : Fin 9) (t : T) : ℂ := if emb t i then -1 else 1

lemma chi_conj (i : Fin 9) (t : T) : conj (chi i t) = chi i t := by
  simp only [chi]; split <;> simp

lemma chi_sq (i : Fin 9) (t : T) : chi i t * chi i t = 1 := by
  simp only [chi]; split <;> norm_num

lemma chi_cast (i : Fin 9) (t : T) : chi i t = ((chiZ i t : ℤ) : ℂ) := by
  simp only [chi, chiZ]; split <;> simp

lemma sgnc_true_cast (t : T) : sgnc true t = ((sgnZ t : ℤ) : ℂ) := by
  simp only [sgnc, sgnZ, Bool.true_and]; split <;> simp

lemma sZ1 : ∑ t : T, sgnZ t = 0 := by decide

lemma sZ2 (i : Fin 9) : ∑ t : T, sgnZ t * chiZ i t = 0 := by decide +revert

set_option maxRecDepth 40000 in
lemma sZ3 (i j : Fin 9) : ∑ t : T, sgnZ t * chiZ i t * chiZ j t = 0 := by decide +revert

lemma sC1 : ∑ t : T, sgnc true t = 0 := by
  simp only [sgnc_true_cast, ← Int.cast_sum, sZ1, Int.cast_zero]

lemma sC2 (i : Fin 9) : ∑ t : T, sgnc true t * chi i t = 0 := by
  simp only [sgnc_true_cast, chi_cast, ← Int.cast_mul, ← Int.cast_sum, sZ2, Int.cast_zero]

lemma sC3 (i j : Fin 9) : ∑ t : T, sgnc true t * chi i t * chi j t = 0 := by
  simp only [sgnc_true_cast, chi_cast, ← Int.cast_mul, ← Int.cast_sum, sZ3, Int.cast_zero]

/-! ## Amplitudes on the codeword support -/

lemma ampP_I (i : Fin 9) (b : Q) : ampP I i b = 1 := rfl
lemma ampP_X (i : Fin 9) (b : Q) : ampP X i b = 1 := rfl

lemma ampP_Y (i : Fin 9) (t : T) : ampP Y i (emb t) = Complex.I * chi i t := by
  simp only [ampP, chi]; split <;> simp

lemma ampP_Z (i : Fin 9) (t : T) : ampP Z i (emb t) = chi i t := by
  simp only [ampP, chi]

/-! ## The master inner-product computation -/

lemma double_sum_delta (A B : T → ℂ) (c : Bool) :
    ∑ t : T, ∑ t' : T, A t * (B t' * (if c = true ∧ t = t' then (1:ℂ) else 0))
      = if c = true then ∑ t : T, A t * B t else 0 := by
  by_cases hc : c = true
  · simp [hc]
  · simp [hc]

lemma inner_op_cw (p q : P1) (i j : Fin 9) (k l : Bool) :
    inner ℂ (op p i (cw k)) (op q j (cw l)) =
      if compat p q i j = true then
        (1/8 : ℂ) * ∑ t : T, conj (sgnc k t * ampP p i (emb t)) * (sgnc l t * ampP q j (emb t))
      else 0 := by
  have key : inner ℂ (∑ t : T, (sgnc k t * ampP p i (emb t)) • eb (flP p i (emb t)))
                     (∑ t : T, (sgnc l t * ampP q j (emb t)) • eb (flP q j (emb t)))
      = if compat p q i j = true then
          ∑ t : T, conj (sgnc k t * ampP p i (emb t)) * (sgnc l t * ampP q j (emb t))
        else 0 := by
    rw [sum_inner]
    simp only [inner_smul_left, inner_sum, inner_smul_right, inner_eb, flP_emb_eq_iff,
      Finset.mul_sum]
    exact double_sum_delta _ _ _
  rw [op_cw, op_cw, inner_smul_left, inner_smul_right, key, ← mul_assoc, nrm_sq]
  split <;> simp

lemma inner_op_cw_pos (p q : P1) (i j : Fin 9) (k l : Bool) (hc : compat p q i j = true) :
    inner ℂ (op p i (cw k)) (op q j (cw l)) =
      (1/8 : ℂ) * ∑ t : T, conj (sgnc k t * ampP p i (emb t)) * (sgnc l t * ampP q j (emb t)) := by
  rw [inner_op_cw, if_pos hc]

lemma summand_diag (k : Bool) (a b : ℂ) (t : T) :
    conj (sgnc k t * a) * (sgnc k t * b) = conj a * b := by
  rw [map_mul, sgnc_conj]
  linear_combination (conj a * b) * sgnc_sq k t

lemma KL_diag (p q : P1) (i j : Fin 9) (k : Bool) :
    inner ℂ (op p i (cw k)) (op q j (cw k))
      = inner ℂ (op p i (cw false)) (op q j (cw false)) := by
  rw [inner_op_cw, inner_op_cw]
  simp only [summand_diag]

lemma sum_of_zero (c : ℂ) (f : T → ℂ) (h : ∑ t : T, f t = 0) : ∑ t : T, c * f t = 0 := by
  rw [← Finset.mul_sum, h, mul_zero]

lemma off_sum (p q : P1) (i j : Fin 9) (hc : compat p q i j = true) :
    ∑ t : T, sgnc true t * (conj (ampP p i (emb t)) * ampP q j (emb t)) = 0 := by
  cases p <;> cases q
  · -- I, I
    have h : ∀ t : T, sgnc true t * (conj (ampP I i (emb t)) * ampP I j (emb t))
        = 1 * sgnc true t := by intro t; simp [ampP_I]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ sC1
  · exact absurd hc (by simp [compat, flips])
  · exact absurd hc (by simp [compat, flips])
  · -- I, Z
    have h : ∀ t : T, sgnc true t * (conj (ampP I i (emb t)) * ampP Z j (emb t))
        = 1 * (sgnc true t * chi j t) := by intro t; simp [ampP_I, ampP_Z]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ (sC2 j)
  · exact absurd hc (by simp [compat, flips])
  · -- X, X
    have h : ∀ t : T, sgnc true t * (conj (ampP X i (emb t)) * ampP X j (emb t))
        = 1 * sgnc true t := by intro t; simp [ampP_X]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ sC1
  · -- X, Y
    have hij : i = j := by simpa [compat, flips] using hc
    subst hij
    have h : ∀ t : T, sgnc true t * (conj (ampP X i (emb t)) * ampP Y i (emb t))
        = Complex.I * (sgnc true t * chi i t) := by
      intro t; rw [ampP_X, ampP_Y]; simp; ring
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero _ _ (sC2 i)
  · exact absurd hc (by simp [compat, flips])
  · exact absurd hc (by simp [compat, flips])
  · -- Y, X
    have hij : i = j := by simpa [compat, flips] using hc
    subst hij
    have h : ∀ t : T, sgnc true t * (conj (ampP Y i (emb t)) * ampP X i (emb t))
        = (-Complex.I) * (sgnc true t * chi i t) := by
      intro t; rw [ampP_X, ampP_Y]; simp [chi_conj]; ring
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero _ _ (sC2 i)
  · -- Y, Y
    have hij : i = j := by simpa [compat, flips] using hc
    subst hij
    have h : ∀ t : T, sgnc true t * (conj (ampP Y i (emb t)) * ampP Y i (emb t))
        = 1 * sgnc true t := by
      intro t
      rw [ampP_Y]
      have h2 := chi_sq i t
      simp only [map_mul, Complex.conj_I, chi_conj]
      linear_combination (sgnc true t) * h2
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ sC1
  · exact absurd hc (by simp [compat, flips])
  · -- Z, I
    have h : ∀ t : T, sgnc true t * (conj (ampP Z i (emb t)) * ampP I j (emb t))
        = 1 * (sgnc true t * chi i t) := by intro t; simp [ampP_I, ampP_Z, chi_conj]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ (sC2 i)
  · exact absurd hc (by simp [compat, flips])
  · exact absurd hc (by simp [compat, flips])
  · -- Z, Z
    have h : ∀ t : T, sgnc true t * (conj (ampP Z i (emb t)) * ampP Z j (emb t))
        = 1 * (sgnc true t * chi i t * chi j t) := by
      intro t; simp [ampP_Z, chi_conj]; ring
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ (sC3 i j)

lemma KL_off (p q : P1) (i j : Fin 9) :
    inner ℂ (op p i (cw false)) (op q j (cw true)) = 0 := by
  rw [inner_op_cw]
  split
  · rename_i hc
    have h : ∀ t : T, conj (sgnc false t * ampP p i (emb t)) * (sgnc true t * ampP q j (emb t))
        = sgnc true t * (conj (ampP p i (emb t)) * ampP q j (emb t)) := by
      intro t; rw [sgnc_false]; simp; ring
    rw [Finset.sum_congr rfl (fun t _ => h t), off_sum p q i j hc, mul_zero]
  · rfl

lemma KL_off' (p q : P1) (i j : Fin 9) :
    inner ℂ (op p i (cw true)) (op q j (cw false)) = 0 := by
  have h := KL_off q p j i
  rw [← inner_conj_symm] at h
  simpa using h

lemma inner_cw_diag (k : Bool) : inner ℂ (cw k) (cw k) = 1 := by
  have hc : compat I I 0 0 = true := by decide
  rw [← op_I 0 (cw k), inner_op_cw_pos _ _ _ _ _ _ hc]
  simp only [summand_diag, ampP_I, map_one, one_mul]
  simp
  norm_num

lemma inner_cw (k l : Bool) : inner ℂ (cw k) (cw l) = if k = l then 1 else 0 := by
  cases k <;> cases l
  · simpa using inner_cw_diag false
  · have h := KL_off I I 0 0
    rw [op_I, op_I] at h
    simpa using h
  · have h := KL_off' I I 0 0
    rw [op_I, op_I] at h
    simpa using h
  · simpa using inner_cw_diag true

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

