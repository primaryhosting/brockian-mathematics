/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring to precede the `import` line; the text is otherwise verbatim.)

import Mathlib

/-!
## Overview

We work with the state space of nine qubits, `ℂ^(2^9)`, realized concretely as the space
`St = (Fin 9 → Bool) → ℂ` of complex-valued functions on the computational basis labels
`Qbits = Fin 9 → Bool`, with the standard Hermitian inner product `ip`.

The nine-qubit Shor code is the two-dimensional subspace spanned by the orthonormal logical
states

  `|0_L⟩ = 2^(-3/2) (|000⟩+|111⟩)(|000⟩+|111⟩)(|000⟩+|111⟩)`,
  `|1_L⟩ = 2^(-3/2) (|000⟩-|111⟩)(|000⟩-|111⟩)(|000⟩-|111⟩)`.

An *arbitrary single-qubit error* on qubit `k` is an arbitrary linear operator acting on the
`k`-th tensor factor and as the identity elsewhere; it is described by an arbitrary `2 × 2`
complex matrix `M : Bool → Bool → ℂ` through the operator `qubitOp k M`.

The final theorem `QI.shor_code_corrects` states:

* the logical states are orthonormal (so the code is a genuine two-dimensional code), and
* the Knill–Laflamme error-correction conditions hold for the set of all single-qubit errors:
  for all qubits `k, l` and all single-qubit operators `M, N`,
  `⟨i_L| (qubitOp k M)† (qubitOp l N) |j_L⟩ = γ δ_{ij}`
  for a scalar `γ` depending only on the errors and not on the logical state.

The Knill–Laflamme conditions are the standard necessary and sufficient criterion for the
existence of a recovery channel correcting the given error set; since the set of single-qubit
errors is closed under the operations involved, this says precisely that the Shor code corrects
an arbitrary single-qubit error.
-/

namespace QI

open Finset

/-- Computational basis labels for nine qubits. -/
abbrev Qbits : Type := Fin 9 → Bool

/-- The state space of nine qubits, `ℂ^(2^9)`, as functions on basis labels. -/
abbrev St : Type := Qbits → ℂ

/-- The standard Hermitian inner product, conjugate linear in the first variable. -/
noncomputable def ip (u v : St) : ℂ := ∑ q, (starRingEnd ℂ) (u q) * v q

/-- Flip the `k`-th bit of a basis label. -/
def flipAt (k : Fin 9) (q : Qbits) : Qbits := fun i => if i = k then !q i else q i

/-- Set the `k`-th bit of a basis label to `b`. -/
def setAt (k : Fin 9) (b : Bool) (q : Qbits) : Qbits := fun i => if i = k then b else q i

/-- The four single-qubit Pauli matrices. -/
inductive Pauli | I | X | Y | Z
deriving DecidableEq

/-- The Pauli operator `p` acting on qubit `k` of a nine-qubit state. -/
noncomputable def Pop : Pauli → Fin 9 → St → St
  | Pauli.I, _, v => v
  | Pauli.X, k, v => fun q => v (flipAt k q)
  | Pauli.Y, k, v => fun q => (if q k then Complex.I else -Complex.I) * v (flipAt k q)
  | Pauli.Z, k, v => fun q => (if q k then -1 else 1) * v q

/-- The operator on nine qubits given by the `2 × 2` matrix `M` acting on qubit `k` and the
identity on the other eight qubits.  This is the general form of a single-qubit error. -/
noncomputable def qubitOp (k : Fin 9) (M : Bool → Bool → ℂ) (v : St) : St :=
  fun q => ∑ b : Bool, M (q k) b * v (setAt k b q)

/-- The basis label all of whose three blocks of three qubits are constant, with values
`s.1`, `s.2.1`, `s.2.2`. -/
def cst (s : Bool × Bool × Bool) : Qbits :=
  fun i => if i.val < 3 then s.1 else if i.val < 6 then s.2.1 else s.2.2

/-- The sign `(-1)^b`. -/
def chi (b : Bool) : ℂ := if b then -1 else 1

/-- Coefficients of the two logical states in the basis `cst s`. -/
def co : Bool → (Bool × Bool × Bool) → ℂ
  | false, _ => 1
  | true, s => chi s.1 * chi s.2.1 * chi s.2.2

/-- The (unnormalized) logical states of the Shor code. -/
noncomputable def ulog (i : Bool) : St := fun q => ∑ s, co i s * (if q = cst s then 1 else 0)

/-- The normalized logical states `|0_L⟩` and `|1_L⟩` of the nine-qubit Shor code. -/
noncomputable def shor (i : Bool) : St := fun q => (1 / (2 * Real.sqrt 2) : ℝ) * ulog i q

/-- Selecting the value of the `m`-th block. -/
def sel : Fin 3 → (Bool × Bool × Bool) → Bool
  | 0, s => s.1
  | 1, s => s.2.1
  | _, s => s.2.2

/-- The block (of three qubits) containing qubit `k`. -/
def bidx (k : Fin 9) : Fin 3 := ⟨k.val / 3, by omega⟩

/-! ## Elementary properties of the inner product -/

lemma ip_add_left (u w v : St) : ip (fun q => u q + w q) v = ip u v + ip w v := by
  simp only [ip, map_add, add_mul, Finset.sum_add_distrib]

lemma ip_add_right (u v w : St) : ip u (fun q => v q + w q) = ip u v + ip u w := by
  simp only [ip, mul_add, Finset.sum_add_distrib]

lemma ip_smul_left (a : ℂ) (u v : St) :
    ip (fun q => a * u q) v = (starRingEnd ℂ) a * ip u v := by
  simp only [ip, map_mul, Finset.mul_sum, mul_assoc]

lemma ip_smul_right (a : ℂ) (u v : St) : ip u (fun q => a * v q) = a * ip u v := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma ip_sum_left {ι : Type} [Fintype ι] (f : ι → St) (v : St) :
    ip (fun q => ∑ k, f k q) v = ∑ k, ip (f k) v := by
  simp only [ip, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ip_sum_right {ι : Type} [Fintype ι] (u : St) (f : ι → St) :
    ip u (fun q => ∑ k, f k q) = ∑ k, ip u (f k) := by
  simp only [ip, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ## Basic combinatorics of the block structure -/

lemma cst_apply (s : Bool × Bool × Bool) (k : Fin 9) : cst s k = sel (bidx k) s := by
  fin_cases k <;> rfl

lemma cst_block {s : Bool × Bool × Bool} {m k : Fin 9} (h : bidx m = bidx k) :
    cst s m = cst s k := by rw [cst_apply, cst_apply, h]

lemma cst_inj {s t : Bool × Bool × Bool} (h : cst s = cst t) : s = t := by
  have h0 := congrFun h ⟨0, by omega⟩
  have h3 := congrFun h ⟨3, by omega⟩
  have h6 := congrFun h ⟨6, by omega⟩
  simp [cst] at h0 h3 h6
  exact Prod.ext h0 (Prod.ext h3 h6)

lemma exists_partner : ∀ k l : Fin 9, ∃ m : Fin 9, bidx m = bidx k ∧ m ≠ k ∧ m ≠ l := by
  decide

lemma flipAt_invol (k : Fin 9) (q : Qbits) : flipAt k (flipAt k q) = q := by
  funext i; by_cases h : i = k <;> simp [flipAt, h]

lemma flipAt_self (k : Fin 9) (q : Qbits) : flipAt k q k = !q k := by simp [flipAt]

lemma cst_ne_flip1 (k : Fin 9) (s t : Bool × Bool × Bool) : flipAt k (cst s) ≠ cst t := by
  obtain ⟨m, hm, hmk, -⟩ := exists_partner k k
  intro h
  have h1 := congrFun h k
  have h2 := congrFun h m
  simp [flipAt, hmk] at h1 h2
  rw [cst_block (s := t) hm, cst_block (s := s) hm] at h2
  rw [← h2] at h1
  exact (Bool.not_ne_self _) h1.symm

lemma cst_ne_flip2 {k l : Fin 9} (hkl : k ≠ l) (s t : Bool × Bool × Bool) :
    flipAt k (flipAt l (cst s)) ≠ cst t := by
  obtain ⟨m, hm, hmk, hml⟩ := exists_partner k l
  intro h
  have h1 := congrFun h k
  have h2 := congrFun h m
  simp [flipAt, hmk, hml, hkl] at h1 h2
  rw [cst_block (s := t) hm, cst_block (s := s) hm] at h2
  rw [← h2] at h1
  exact (Bool.not_ne_self _) h1.symm

/-! ## Evaluation of the logical states -/

lemma co_conj (i : Bool) (s : Bool × Bool × Bool) : (starRingEnd ℂ) (co i s) = co i s := by
  cases i <;> obtain ⟨a, b, c⟩ := s <;> cases a <;> cases b <;> cases c <;> simp [co, chi]

lemma ulog_cst (i : Bool) (t : Bool × Bool × Bool) : ulog i (cst t) = co i t := by
  simp only [ulog]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    have : cst t ≠ cst b := fun h => hb (cst_inj h).symm
    simp [this]
  · simp

lemma ulog_zero_of_ne (i : Bool) (q : Qbits) (h : ∀ t, q ≠ cst t) : ulog i q = 0 := by
  simp only [ulog]
  exact Finset.sum_eq_zero fun t _ => by simp [h t]

lemma ulog_flip1 (i : Bool) (k : Fin 9) (s : Bool × Bool × Bool) :
    ulog i (flipAt k (cst s)) = 0 :=
  ulog_zero_of_ne i _ (cst_ne_flip1 k s)

lemma ulog_flip2 (i : Bool) {k l : Fin 9} (hkl : k ≠ l) (s : Bool × Bool × Bool) :
    ulog i (flipAt k (flipAt l (cst s))) = 0 :=
  ulog_zero_of_ne i _ (cst_ne_flip2 hkl s)

lemma ip_ulog_left (i : Bool) (v : St) : ip (ulog i) v = ∑ s, co i s * v (cst s) := by
  simp only [ip, ulog, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [co_conj, apply_ite, Finset.sum_ite_eq']

/-! ## Pauli operators are self-adjoint -/

noncomputable def flipEquiv (k : Fin 9) : Qbits ≃ Qbits :=
  Function.Involutive.toPerm (flipAt k) (flipAt_invol k)

lemma sum_flip (k : Fin 9) (f : Qbits → ℂ) : ∑ q, f (flipAt k q) = ∑ q, f q :=
  Fintype.sum_equiv (flipEquiv k) _ _ (fun _ => rfl)

lemma Pop_selfadj (p : Pauli) (k : Fin 9) (u v : St) :
    ip (Pop p k u) v = ip u (Pop p k v) := by
  cases p
  · rfl
  · simp only [ip, Pop]
    rw [← sum_flip k (fun q => (starRingEnd ℂ) (u (flipAt k q)) * v q)]
    exact Finset.sum_congr rfl fun q _ => by rw [flipAt_invol]
  · simp only [ip, Pop]
    rw [← sum_flip k (fun q =>
      (starRingEnd ℂ) ((if q k then Complex.I else -Complex.I) * u (flipAt k q)) * v q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [flipAt_invol, flipAt_self]
    cases q k <;> simp <;> ring
  · simp only [ip, Pop]
    refine Finset.sum_congr rfl fun q _ => ?_
    cases q k <;> simp

lemma Pop_smul (p : Pauli) (k : Fin 9) (a : ℂ) (v : St) :
    Pop p k (fun q => a * v q) = fun q => a * Pop p k v q := by
  cases p <;> funext q <;> simp only [Pop] <;> ring

/-! ## The three sign sums -/

lemma sumS1 (i j : Bool) : ∑ s, co i s * co j s = if i = j then 8 else 0 := by
  cases i <;> cases j <;> norm_num [co, chi, Fintype.sum_prod_type]

lemma sumS2 (i j : Bool) (m : Fin 3) : ∑ s, co i s * (chi (sel m s) * co j s) = 0 := by
  cases i <;> cases j <;> fin_cases m <;>
    simp [co, chi, sel, Fintype.sum_prod_type] <;> norm_num

lemma sumS3 (i j : Bool) (m m' : Fin 3) :
    ∑ s, co i s * (chi (sel m s) * (chi (sel m' s) * co j s))
      = if i = j ∧ m = m' then 8 else 0 := by
  cases i <;> cases j <;> fin_cases m <;> fin_cases m' <;>
    simp [co, chi, sel, Fintype.sum_prod_type] <;> norm_num

/-! ## The Knill–Laflamme matrix for the Pauli basis -/

/-- The Knill–Laflamme coefficient `⟨i_L| P_k P'_l |i_L⟩` for the unnormalized logical states. -/
def klCoeff (p : Pauli) (k : Fin 9) (p' : Pauli) (l : Fin 9) : ℂ :=
  if (p = Pauli.I ∧ p' = Pauli.I) ∨ (p = Pauli.X ∧ p' = Pauli.X ∧ k = l) ∨
     (p = Pauli.Y ∧ p' = Pauli.Y ∧ k = l) ∨ (p = Pauli.Z ∧ p' = Pauli.Z ∧ bidx k = bidx l)
  then 8 else 0

lemma key (p p' : Pauli) (k l : Fin 9) (i j : Bool) :
    ip (Pop p k (ulog i)) (Pop p' l (ulog j)) = if i = j then klCoeff p k p' l else 0 := by
  rw [Pop_selfadj, ip_ulog_left]
  cases p <;> cases p'
  -- (I, I)
  · simp only [Pop, ulog_cst]
    rw [sumS1]
    simp [klCoeff]
  -- (I, X)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (I, Y)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (I, Z)
  · have h : ∀ s : Bool × Bool × Bool,
        co i s * (Pop Pauli.I k (Pop Pauli.Z l (ulog j))) (cst s)
          = co i s * (chi (sel (bidx l) s) * co j s) := by
      intro s; simp [Pop, chi, cst_apply, ulog_cst]
    simp only [h]
    rw [sumS2]
    simp [klCoeff]
  -- (X, I)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (X, X)
  · by_cases hkl : k = l
    · subst hkl
      simp only [Pop, flipAt_invol, ulog_cst]
      rw [sumS1]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (X, Y)
  · by_cases hkl : k = l
    · subst hkl
      have h : ∀ s : Bool × Bool × Bool,
          co i s * (Pop Pauli.X k (Pop Pauli.Y k (ulog j))) (cst s)
            = Complex.I * (co i s * (chi (sel (bidx k) s) * co j s)) := by
        intro s
        simp only [Pop, flipAt_self, flipAt_invol, ulog_cst, chi, cst_apply]
        cases sel (bidx k) s <;> simp <;> ring
      simp only [h]
      rw [← Finset.mul_sum, sumS2, mul_zero]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (X, Z)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Y, I)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Y, X)
  · by_cases hkl : k = l
    · subst hkl
      have h : ∀ s : Bool × Bool × Bool,
          co i s * (Pop Pauli.Y k (Pop Pauli.X k (ulog j))) (cst s)
            = (-Complex.I) * (co i s * (chi (sel (bidx k) s) * co j s)) := by
        intro s
        simp only [Pop, flipAt_invol, ulog_cst, chi, cst_apply]
        cases sel (bidx k) s <;> simp <;> ring
      simp only [h]
      rw [← Finset.mul_sum, sumS2, mul_zero]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (Y, Y)
  · by_cases hkl : k = l
    · subst hkl
      have h : ∀ s : Bool × Bool × Bool,
          co i s * (Pop Pauli.Y k (Pop Pauli.Y k (ulog j))) (cst s) = co i s * co j s := by
        intro s
        simp only [Pop, flipAt_self, flipAt_invol, ulog_cst]
        cases cst s k <;> simp <;> ring_nf <;> rw [Complex.I_sq] <;> ring
      simp only [h]
      rw [sumS1]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (Y, Z)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Z, I)
  · have h : ∀ s : Bool × Bool × Bool,
        co i s * (Pop Pauli.Z k (Pop Pauli.I l (ulog j))) (cst s)
          = co i s * (chi (sel (bidx k) s) * co j s) := by
      intro s; simp [Pop, chi, cst_apply, ulog_cst]
    simp only [h]
    rw [sumS2]
    simp [klCoeff]
  -- (Z, X)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Z, Y)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Z, Z)
  · have h : ∀ s : Bool × Bool × Bool,
        co i s * (Pop Pauli.Z k (Pop Pauli.Z l (ulog j))) (cst s)
          = co i s * (chi (sel (bidx k) s) * (chi (sel (bidx l) s) * co j s)) := by
      intro s; simp [Pop, chi, cst_apply, ulog_cst]
    simp only [h]
    rw [sumS3]
    by_cases hij : i = j <;> by_cases hb : bidx k = bidx l <;> simp [klCoeff, hij, hb]

/-! ## Normalization of the logical states -/

lemma ip_ulog (i j : Bool) : ip (ulog i) (ulog j) = if i = j then 8 else 0 := by
  rw [ip_ulog_left]
  simp only [ulog_cst]
  exact sumS1 i j

lemma sqrt_two_coeff :
    ((1 / (2 * Real.sqrt 2) : ℝ) : ℂ) * ((1 / (2 * Real.sqrt 2) : ℝ) : ℂ) = 1 / 8 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h : (1 / (2 * Real.sqrt 2) : ℝ) * (1 / (2 * Real.sqrt 2)) = 1 / 8 := by
    rw [div_mul_div_comm, show (2 * Real.sqrt 2) * (2 * Real.sqrt 2)
      = 4 * (Real.sqrt 2 * Real.sqrt 2) by ring, h2]
    norm_num
  rw [← Complex.ofReal_mul, h]
  norm_num

lemma shor_def (i : Bool) :
    shor i = fun q => ((1 / (2 * Real.sqrt 2) : ℝ) : ℂ) * ulog i q := rfl

/-- The logical states of the Shor code are orthonormal. -/
lemma ip_shor (i j : Bool) : ip (shor i) (shor j) = if i = j then 1 else 0 := by
  simp only [shor_def, ip_smul_left, ip_smul_right, Complex.conj_ofReal]
  rw [ip_ulog, ← mul_assoc, sqrt_two_coeff]
  cases i <;> cases j <;> norm_num

/-! ## Arbitrary single-qubit errors -/

/-- A single-qubit error on qubit `k` written in the Pauli basis. -/
noncomputable def err (k : Fin 9) (c : Pauli → ℂ) (v : St) : St := fun q =>
  c Pauli.I * Pop Pauli.I k v q + c Pauli.X * Pop Pauli.X k v q
    + c Pauli.Y * Pop Pauli.Y k v q + c Pauli.Z * Pop Pauli.Z k v q

lemma err_def (k : Fin 9) (c : Pauli → ℂ) (v : St) : err k c v = fun q =>
    c Pauli.I * Pop Pauli.I k v q + c Pauli.X * Pop Pauli.X k v q
      + c Pauli.Y * Pop Pauli.Y k v q + c Pauli.Z * Pop Pauli.Z k v q := rfl

/-- The Pauli coordinates of a `2 × 2` matrix. -/
noncomputable def paulify (M : Bool → Bool → ℂ) : Pauli → ℂ
  | Pauli.I => (M false false + M true true) / 2
  | Pauli.X => (M false true + M true false) / 2
  | Pauli.Y => Complex.I * (M false true - M true false) / 2
  | Pauli.Z => (M false false - M true true) / 2

lemma setAt_of_eq {k : Fin 9} {q : Qbits} {b : Bool} (h : q k = b) : setAt k b q = q := by
  funext i
  by_cases hi : i = k
  · subst hi; simp [setAt, h]
  · simp [setAt, hi]

lemma setAt_of_ne {k : Fin 9} {q : Qbits} {b : Bool} (h : q k = !b) :
    setAt k b q = flipAt k q := by
  funext i
  by_cases hi : i = k
  · subst hi; simp [setAt, flipAt, h]
  · simp [setAt, flipAt, hi]

/-- Every operator acting on a single qubit is a linear combination of Pauli operators on that
qubit:  the general single-qubit error `qubitOp k M` equals `err k (paulify M)`. -/
lemma qubitOp_eq_err (k : Fin 9) (M : Bool → Bool → ℂ) (v : St) :
    qubitOp k M v = err k (paulify M) v := by
  funext q
  simp only [qubitOp, err, Pop, paulify, Fintype.sum_bool]
  cases hb : q k
  · rw [setAt_of_eq hb, setAt_of_ne (b := true) (by simp [hb])]
    simp only [Bool.false_eq_true, if_false]
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [setAt_of_eq hb, setAt_of_ne (b := false) (by simp [hb])]
    simp only [if_true]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The Knill–Laflamme scalar attached to a pair of single-qubit errors. -/
noncomputable def klSum (k l : Fin 9) (c d : Pauli → ℂ) : ℂ :=
  (starRingEnd ℂ) (c Pauli.I) * d Pauli.I
    + (if k = l then (starRingEnd ℂ) (c Pauli.X) * d Pauli.X
        + (starRingEnd ℂ) (c Pauli.Y) * d Pauli.Y else 0)
    + (if bidx k = bidx l then (starRingEnd ℂ) (c Pauli.Z) * d Pauli.Z else 0)

lemma key_shor (p p' : Pauli) (k l : Fin 9) (i j : Bool) :
    ip (Pop p k (shor i)) (Pop p' l (shor j))
      = if i = j then klCoeff p k p' l / 8 else 0 := by
  simp only [shor_def, Pop_smul, ip_smul_left, ip_smul_right, Complex.conj_ofReal]
  rw [key, ← mul_assoc, sqrt_two_coeff]
  split <;> ring

/-- The Knill–Laflamme conditions for the Shor code, in the Pauli parametrization. -/
lemma ip_err (k l : Fin 9) (c d : Pauli → ℂ) (i j : Bool) :
    ip (err k c (shor i)) (err l d (shor j)) = if i = j then klSum k l c d else 0 := by
  simp only [err_def, ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, key_shor]
  by_cases hij : i = j
  · simp only [hij, if_true, klSum, klCoeff]
    by_cases hkl : k = l
    · simp [hkl]; ring
    · by_cases hbb : bidx k = bidx l <;> simp [hkl, hbb] <;> ring
  · simp [hij]

/-!
## Main theorem
-/

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

The first conjunct says that the two logical states `shor false = |0_L⟩` and `shor true = |1_L⟩`
are orthonormal, so that the Shor code is a genuine two-dimensional quantum code inside the
`2^9`-dimensional nine-qubit state space.

The second conjunct is the Knill–Laflamme error-correction condition for the set of all
single-qubit errors:  for any two qubits `k, l` and any two single-qubit operators `M, N`
(arbitrary `2 × 2` complex matrices acting on qubit `k`, resp. `l`, and as the identity
elsewhere), the matrix elements `⟨i_L| (qubitOp k M)† (qubitOp l N) |j_L⟩` vanish off the
diagonal and are equal to one and the same scalar `γ` on the diagonal, independently of the
logical state.  This is the necessary and sufficient criterion for the existence of a recovery
operation undoing an arbitrary error on any single one of the nine qubits. -/
theorem shor_code_corrects :
    (∀ i j : Bool, ip (shor i) (shor j) = if i = j then 1 else 0) ∧
    (∀ (k l : Fin 9) (M N : Bool → Bool → ℂ), ∃ γ : ℂ, ∀ i j : Bool,
      ip (qubitOp k M (shor i)) (qubitOp l N (shor j)) = if i = j then γ else 0) := by
  refine ⟨ip_shor, fun k l M N => ⟨klSum k l (paulify M) (paulify N), fun i j => ?_⟩⟩
  rw [qubitOp_eq_err, qubitOp_eq_err]
  exact ip_err k l _ _ i j

/-- **The correctable error set is the whole linear span of the single-qubit errors.**

The Knill–Laflamme conditions also hold for arbitrary linear combinations
`∑ k, qubitOp k (Ms k)` of single-qubit errors on the nine qubits, which is the linear span of
the set of single-qubit errors. -/
theorem shor_code_corrects_span (Ms Ns : Fin 9 → Bool → Bool → ℂ) :
    ∃ γ : ℂ, ∀ i j : Bool,
      ip (fun q => ∑ k, qubitOp k (Ms k) (shor i) q)
        (fun q => ∑ l, qubitOp l (Ns l) (shor j) q) = if i = j then γ else 0 := by
  refine ⟨∑ k, ∑ l, klSum k l (paulify (Ms k)) (paulify (Ns l)), fun i j => ?_⟩
  rw [ip_sum_left]
  simp only [ip_sum_right]
  have h : ∀ k l : Fin 9,
      ip (qubitOp k (Ms k) (shor i)) (qubitOp l (Ns l) (shor j))
        = if i = j then klSum k l (paulify (Ms k)) (paulify (Ns l)) else 0 := by
    intro k l
    rw [qubitOp_eq_err, qubitOp_eq_err]
    exact ip_err k l _ _ i j
  simp only [h]
  by_cases hij : i = j <;> simp [hij]

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

