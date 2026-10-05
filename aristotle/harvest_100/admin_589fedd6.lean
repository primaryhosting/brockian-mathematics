import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace QI

/-! ## Setup

Nine qubits, indexed by `Idx = Fin 3 × Fin 3`: the first component is the block
(one of the three "outer" repetition-code slots), the second is the position of the
qubit inside its block.  A computational basis state is a bit string `Idx → Bool`,
and the state space is the corresponding `512`-dimensional complex Hilbert space. -/

/-- Index of a qubit: `(block, position within block)`. -/
abbrev Idx := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev BasisIdx := Idx → Bool

/-- The nine-qubit state space. -/
abbrev QState := EuclideanSpace ℂ BasisIdx

/-- The operator acting as the `2 × 2` matrix `M` on qubit `q` and as the identity
on the remaining eight qubits.  Every single-qubit error on qubit `q` is of this form. -/
noncomputable def qubitOp (q : Idx) (M : Bool → Bool → ℂ) : QState →ₗ[ℂ] QState where
  toFun f := (WithLp.toLp 2 (fun x => ∑ b : Bool, M (x q) b * f (Function.update x q b)))
  map_add' f g := by ext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext x; simp; ring

/-- The value carried by block `i` in a triple of block values. -/
def blockVal (s : Bool × Bool × Bool) (i : Fin 3) : Bool := ![s.1, s.2.1, s.2.2] i

/-- The basis state in which every qubit of block `i` carries the value `blockVal s i`;
these are exactly the basis states occurring in the Shor codewords. -/
def emb (s : Bool × Bool × Bool) : BasisIdx := fun p => blockVal s p.1

/-- The computational basis vector attached to `emb s`. -/
noncomputable def bvec (s : Bool × Bool × Bool) : QState := EuclideanSpace.single (emb s) (1 : ℂ)

/-- The sign `(-1)^{|s|}` for the logical `1`, and `1` for the logical `0`. -/
def sgn (a : Bool) (s : Bool × Bool × Bool) : ℂ :=
  if a then (if s.1 then -1 else 1) * (if s.2.1 then -1 else 1) * (if s.2.2 then -1 else 1) else 1

/-- The Shor codewords:
`|0_L⟩ = 8^{-1/2} (|000⟩+|111⟩)^{⊗3}` and `|1_L⟩ = 8^{-1/2} (|000⟩-|111⟩)^{⊗3}`. -/
noncomputable def codeword (a : Bool) : QState :=
  ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ • ∑ s : Bool × Bool × Bool, sgn a s • bvec s

/-! ## Matrix elements -/

lemma qubitOp_single_apply (q : Idx) (M : Bool → Bool → ℂ) (y x : BasisIdx) :
    (qubitOp q M) (EuclideanSpace.single y (1 : ℂ)) x =
      if Function.update x q (y q) = y then M (x q) (y q) else 0 := by
  show ∑ b : Bool, M (x q) b * (EuclideanSpace.single y (1:ℂ)) (Function.update x q b) = _
  rw [Finset.sum_eq_single (y q)]
  · simp [EuclideanSpace.single_apply]
  · intro b _ hb
    simp only [EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro h
    exact absurd (by rw [← h]; simp) hb
  · simp

lemma inner_apply (f g : QState) : ⟪f, g⟫_ℂ = ∑ x, conj (f x) * g x := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- If two bit strings of the form `emb s`, `emb t` agree off two qubits `q`, `r`,
then `s = t`: each block contains a qubit distinct from `q` and from `r`. -/
lemma emb_inj_off_two {s t : Bool × Bool × Bool} {q r : Idx}
    (h : ∀ p : Idx, p ≠ q → p ≠ r → emb s p = emb t p) : s = t := by
  have key : ∀ (q r : Idx) (i : Fin 3), ∃ j : Fin 3, ((i, j) ≠ q ∧ (i, j) ≠ r) := by decide
  have hb : ∀ i, blockVal s i = blockVal t i := by
    intro i
    obtain ⟨j, hj1, hj2⟩ := key q r i
    have := h (i, j) hj1 hj2
    simpa [emb] using this
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
  simp [blockVal] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- The single-qubit "response function": for two single-qubit operators, `M` at `q` and
`N` at `r`, this is the overlap they produce on a codeword basis state, as a function
of the bit values at `q` and at `r`. -/
noncomputable def gmat (q r : Idx) (M N : Bool → Bool → ℂ) (u w : Bool) : ℂ :=
  if q = r then ∑ b : Bool, conj (M b u) * N b u else conj (M u u) * N w w

/-- **Key computation.**  Two single-qubit errors applied to the basis states occurring in
the codewords produce overlapping states only when the underlying block values agree. -/
lemma inner_qubitOp_bvec (q r : Idx) (M N : Bool → Bool → ℂ) (s t : Bool × Bool × Bool) :
    ⟪qubitOp q M (bvec s), qubitOp r N (bvec t)⟫_ℂ =
      if s = t then gmat q r M N (emb s q) (emb s r) else 0 := by
  rw [inner_apply]
  simp only [bvec, qubitOp_single_apply]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    by_cases hqr : q = r
    · -- same qubit: two basis states contribute
      subst hqr
      rw [Finset.sum_eq_add_of_mem (Function.update (emb s) q false)
          (Function.update (emb s) q true) (Finset.mem_univ _) (Finset.mem_univ _)]
      · have h1 : Function.update (Function.update (emb s) q false) q (emb s q) = emb s := by
          simp [Function.update_idem]
        have h2 : Function.update (Function.update (emb s) q true) q (emb s q) = emb s := by
          simp [Function.update_idem]
        rw [h1, h2]
        simp only [gmat, Function.update_self, Fintype.sum_bool, if_true]
        ring
      · intro h
        have := congrFun h q
        simp at this
      · rintro x - ⟨hx1, hx2⟩
        by_cases hc : Function.update x q (emb s q) = emb s
        · exfalso
          have hxb : x = Function.update (emb s) q (x q) := by
            funext p
            by_cases hp : p = q
            · subst hp; simp
            · have := congrFun hc p
              rw [Function.update_of_ne hp] at this
              rw [Function.update_of_ne hp, this]
          cases hxq : x q
          · exact hx1 (by rw [hxb, hxq])
          · exact hx2 (by rw [hxb, hxq])
        · simp [hc]
    · -- distinct qubits: only one basis state contributes
      rw [Finset.sum_eq_single_of_mem (emb s) (Finset.mem_univ _)]
      · rw [gmat, if_neg hqr]
        simp
      · rintro x - hx
        by_cases hc1 : Function.update x q (emb s q) = emb s
        · by_cases hc2 : Function.update x r (emb s r) = emb s
          · exfalso
            apply hx
            funext p
            by_cases hp : p = q
            · subst hp
              have := congrFun hc2 p
              rwa [Function.update_of_ne hqr] at this
            · have := congrFun hc1 p
              rwa [Function.update_of_ne hp] at this
          · simp [hc2]
        · simp [hc1]
  · -- different block values: no overlap at all
    rw [if_neg hst]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hc1 : Function.update x q (emb s q) = emb s
    · by_cases hc2 : Function.update x r (emb t r) = emb t
      · exfalso
        apply hst
        apply emb_inj_off_two (q := q) (r := r)
        intro p hp1 hp2
        have e1 := congrFun hc1 p
        have e2 := congrFun hc2 p
        rw [Function.update_of_ne hp1] at e1
        rw [Function.update_of_ne hp2] at e2
        rw [← e1, ← e2]
      · simp [hc2]
    · simp [hc1]

/-! ## Sign bookkeeping -/

lemma conj_sgn (a : Bool) (s : Bool × Bool × Bool) : conj (sgn a s) = sgn a s := by
  cases a <;> (simp only [sgn, Bool.false_eq_true, if_false, if_true]; try split_ifs) <;> simp

lemma sgn_mul_self (a : Bool) (s : Bool × Bool × Bool) : sgn a s * sgn a s = 1 := by
  cases a <;> (simp only [sgn, Bool.false_eq_true, if_false, if_true]; try split_ifs) <;> ring

lemma sgn_mul_sgn_of_ne {a b : Bool} (h : a ≠ b) (s : Bool × Bool × Bool) :
    sgn a s * sgn b s = sgn true s := by
  cases a <;> cases b <;> simp_all [sgn]

/-- The cancellation making the off-diagonal Knill–Laflamme conditions vanish: a function of
the block values at only two of the three blocks is orthogonal to the sign `(-1)^{|s|}`. -/
lemma sum_sgn_true_mul (i j : Fin 3) (g : Bool → Bool → ℂ) :
    ∑ s : Bool × Bool × Bool, sgn true s * g (blockVal s i) (blockVal s j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [sgn, blockVal, Fintype.sum_prod_type] <;> ring

/-! ## The main theorem -/

lemma inner_codeword_errors (q r : Idx) (M N : Bool → Bool → ℂ) (a b : Bool) :
    ⟪qubitOp q M (codeword a), qubitOp r N (codeword b)⟫_ℂ =
      (8 : ℂ)⁻¹ * ∑ s : Bool × Bool × Bool,
        sgn a s * sgn b s * gmat q r M N (blockVal s q.1) (blockVal s r.1) := by
  have h8 : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  have hnorm : conj (((Real.sqrt 8 : ℝ) : ℂ)⁻¹) * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = (8 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.conj_ofReal, Complex.ofReal_inv, ← mul_inv, h8]
  simp only [codeword, map_smul, map_sum, inner_smul_left, inner_smul_right, sum_inner, inner_sum,
    conj_sgn, inner_qubitOp_bvec, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← hnorm]
  show _ = _ * (sgn a s * sgn b s * gmat q r M N (emb s q) (emb s r))
  ring

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

`codeword false` and `codeword true` are the two Shor codewords, and `qubitOp q M` is an
arbitrary operator acting on the single qubit `q` (an arbitrary `2 × 2` matrix `M` there,
the identity elsewhere).  The statement is the Knill–Laflamme error-correction condition
`⟪E ψ_a, F ψ_b⟫ = c_{E,F} δ_{a,b}` for any two such single-qubit errors `E`, `F`, which is
exactly the necessary and sufficient condition for the code to correct the error set of all
single-qubit operators. -/
theorem shor_code_corrects (q r : Idx) (M N : Bool → Bool → ℂ) :
    ∃ c : ℂ, ∀ a b : Bool,
      ⟪qubitOp q M (codeword a), qubitOp r N (codeword b)⟫_ℂ = if a = b then c else 0 := by
  refine ⟨(8 : ℂ)⁻¹ * ∑ s : Bool × Bool × Bool,
      gmat q r M N (blockVal s q.1) (blockVal s r.1), ?_⟩
  intro a b
  rw [inner_codeword_errors]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by rw [sgn_mul_self, one_mul])
  · rw [if_neg hab]
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn b s * gmat q r M N (blockVal s q.1) (blockVal s r.1) =
          sgn true s * gmat q r M N (blockVal s q.1) (blockVal s r.1) := by
      intro s; rw [sgn_mul_sgn_of_ne hab]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_sgn_true_mul, mul_zero]

/-! ## Nondegeneracy and error detection -/

/-- The identity `2 × 2` matrix, i.e. the trivial (no-)error on a qubit. -/
def idMat : Bool → Bool → ℂ := fun u v => if u = v then 1 else 0

lemma qubitOp_idMat (q : Idx) (f : QState) : qubitOp q idMat f = f := by
  ext x
  show ∑ c : Bool, idMat (x q) c * f (Function.update x q c) = f x
  rw [Finset.sum_eq_single (x q)] <;> simp +contextual [idMat]

lemma gmat_idMat_left (q : Idx) (N : Bool → Bool → ℂ) (u w : Bool) :
    gmat q q idMat N u w = N u u := by
  rw [gmat, if_pos rfl]
  cases u <;> simp [idMat]

/-- Summing the diagonal of a matrix at the value of one block, over all block-value triples. -/
lemma sum_blockVal (i : Fin 3) (P : Bool → Bool → ℂ) :
    ∑ s : Bool × Bool × Bool, P (blockVal s i) (blockVal s i) =
      4 * (P false false + P true true) := by
  fin_cases i <;> simp [blockVal, Fintype.sum_prod_type] <;> ring

/-- The two Shor codewords are orthonormal, so the code space is genuinely two dimensional
and the error-correction conditions above are not vacuous. -/
theorem shor_codewords_orthonormal (a b : Bool) :
    ⟪codeword a, codeword b⟫_ℂ = if a = b then 1 else 0 := by
  rw [← qubitOp_idMat (0, 0) (codeword a), ← qubitOp_idMat (0, 0) (codeword b),
    inner_codeword_errors]
  have hg : ∀ u w : Bool, gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat u w = 1 := by
    intro u w
    rw [gmat_idMat_left]
    cases u <;> simp [idMat]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn a s * gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat
          (blockVal s (0 : Fin 3)) (blockVal s (0 : Fin 3)) = 1 := by
      intro s; rw [sgn_mul_self, one_mul, hg]
    rw [Finset.sum_congr rfl (fun s _ => h s)]
    simp
  · rw [if_neg hab]
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn b s * gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat
            (blockVal s (0 : Fin 3)) (blockVal s (0 : Fin 3)) =
        sgn true s * gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat
            (blockVal s (0 : Fin 3)) (blockVal s (0 : Fin 3)) := by
      intro s; rw [sgn_mul_sgn_of_ne hab]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_sgn_true_mul, mul_zero]

/-- Every traceless single-qubit error (in particular every non-identity Pauli error) maps the
code space into its orthogonal complement: such errors are *detected*. -/
theorem shor_code_detects_traceless (q : Idx) (P : Bool → Bool → ℂ)
    (hP : P false false + P true true = 0) (a b : Bool) :
    ⟪codeword a, qubitOp q P (codeword b)⟫_ℂ = 0 := by
  rw [← qubitOp_idMat q (codeword a), inner_codeword_errors]
  simp only [gmat_idMat_left]
  by_cases hab : a = b
  · subst hab
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn a s * P (blockVal s q.1) (blockVal s q.1) =
          P (blockVal s q.1) (blockVal s q.1) := by
      intro s; rw [sgn_mul_self, one_mul]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_blockVal q.1 P, hP, mul_zero, mul_zero]
  · have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn b s * P (blockVal s q.1) (blockVal s q.1) =
          sgn true s * P (blockVal s q.1) (blockVal s q.1) := by
      intro s; rw [sgn_mul_sgn_of_ne hab]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_sgn_true_mul, mul_zero]

/-- The Pauli `X` matrix. -/
def pauliX : Bool → Bool → ℂ := fun u v => if u = v then 0 else 1

/-- The Pauli `Y` matrix. -/
def pauliY : Bool → Bool → ℂ := fun u v => if u = v then 0 else if u then Complex.I else -Complex.I

/-- The Pauli `Z` matrix. -/
def pauliZ : Bool → Bool → ℂ := fun u v => if u = v then (if u then -1 else 1) else 0

theorem shor_code_detects_X (q : Idx) (a b : Bool) :
    ⟪codeword a, qubitOp q pauliX (codeword b)⟫_ℂ = 0 :=
  shor_code_detects_traceless q pauliX (by simp [pauliX]) a b

theorem shor_code_detects_Y (q : Idx) (a b : Bool) :
    ⟪codeword a, qubitOp q pauliY (codeword b)⟫_ℂ = 0 :=
  shor_code_detects_traceless q pauliY (by simp [pauliY]) a b

theorem shor_code_detects_Z (q : Idx) (a b : Bool) :
    ⟪codeword a, qubitOp q pauliZ (codeword b)⟫_ℂ = 0 :=
  shor_code_detects_traceless q pauliZ (by simp [pauliZ]) a b

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

