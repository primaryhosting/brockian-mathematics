/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace QI

/-! ## Basic types

A computational basis state of one *block* of three qubits is a function `Fin 3 → Bool`;
a computational basis state of the nine qubits of the Shor code is a function
`Fin 3 → Blk`, i.e. three blocks of three qubits.  A qubit is addressed by a pair
`q : Q = Fin 3 × Fin 3` (block index, position inside the block). -/

/-- Computational basis states of one three-qubit block. -/
abbrev Blk := Fin 3 → Bool

/-- Computational basis states of the nine qubits. -/
abbrev Bas := Fin 3 → Blk

/-- Addresses of the nine qubits. -/
abbrev Q := Fin 3 × Fin 3

/-- Bitwise `xor` on a block. -/
def bxorB (u v : Blk) : Blk := fun k => xor (u k) (v k)

/-- Bitwise `xor` on the nine qubits. -/
def bxorb (x y : Bas) : Bas := fun j => bxorB (x j) (y j)

/-- The sign `(-1) ^ (number of positions where `w` and `β` are both `true`)`. -/
def sgnB (w β : Blk) : ℤ := ∏ k, (if w k && β k then (-1 : ℤ) else 1)

/-- The sign `(-1) ^ (number of qubits where `z` and `b` are both `true`)`. -/
def sgnb (z b : Bas) : ℤ := ∏ j, sgnB (z j) (b j)

/-- The all-`false` block. -/
def zeroB : Blk := fun _ => false

/-- The all-`true` block. -/
def oneB : Blk := fun _ => true

/-- The all-`false` basis state. -/
def zeroBas : Bas := fun _ => zeroB

/-- The block indicator of the position `k₀`. -/
def eBlk (k₀ : Fin 3) : Blk := fun k => decide (k = k₀)

/-- The indicator of the qubit `q`. -/
def eQ (q : Q) : Bas := fun j k => decide (j = q.1) && decide (k = q.2)

/-! ## Elementary facts about `xor` and signs -/

@[simp] lemma bxorB_zero_left (u : Blk) : bxorB zeroB u = u := by
  funext k; simp [bxorB, zeroB]

@[simp] lemma bxorb_zero_left (x : Bas) : bxorb zeroBas x = x := by
  funext j; simp [bxorb, zeroBas]

lemma bxorB_involutive (u β : Blk) : bxorB u (bxorB u β) = β := by
  funext k; simp [bxorB]

lemma bxorb_involutive (x b : Bas) : bxorb x (bxorb x b) = b := by
  funext j; exact bxorB_involutive _ _

lemma bxorB_left_comm (u v β : Blk) : bxorB v (bxorB u β) = bxorB (bxorB u v) β := by
  funext k
  simp only [bxorB]
  cases u k <;> cases v k <;> cases β k <;> rfl

lemma bxorb_left_comm (x y b : Bas) : bxorb y (bxorb x b) = bxorb (bxorb x y) b := by
  funext j; exact bxorB_left_comm _ _ _

lemma sgnB_mul (w w' β : Blk) : sgnB w β * sgnB w' β = sgnB (bxorB w w') β := by
  revert w w' β; decide

lemma sgnb_mul (z z' b : Bas) : sgnb z b * sgnb z' b = sgnb (bxorb z z') b := by
  simp only [sgnb, bxorb, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => sgnB_mul _ _ _

lemma sgnB_xor_arg (w u β : Blk) : sgnB w (bxorB u β) = sgnB w u * sgnB w β := by
  revert w u β; decide

lemma sgnb_xor_arg (z x b : Bas) : sgnb z (bxorb x b) = sgnb z x * sgnb z b := by
  simp only [sgnb, bxorb, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => sgnB_xor_arg _ _ _

@[simp] lemma sgnB_zero (β : Blk) : sgnB zeroB β = 1 := by
  revert β; decide

@[simp] lemma sgnb_zero (b : Bas) : sgnb zeroBas b = 1 := by
  simp [sgnb, zeroBas]

lemma sgnB_eBlk (k₀ : Fin 3) (β : Blk) : sgnB (eBlk k₀) β = if β k₀ then -1 else 1 := by
  revert k₀ β; decide

/-! ## The Shor codewords

The (unnormalised) logical states are
`|0_L⟩ = (|000⟩+|111⟩)^{⊗3}` and `|1_L⟩ = (|000⟩-|111⟩)^{⊗3}`,
whose amplitudes in the computational basis are integers. -/

/-- Amplitude, on one block, of `|000⟩ + |111⟩` (`s = false`) resp. `|000⟩ - |111⟩` (`s = true`). -/
def fBlk (s : Bool) (β : Blk) : ℤ :=
  if β 0 = false ∧ β 1 = false ∧ β 2 = false then 1
  else if β 0 = true ∧ β 1 = true ∧ β 2 = true then (if s then -1 else 1)
  else 0

/-- Integer amplitudes of the unnormalised Shor codewords. -/
def czw (s : Bool) (b : Bas) : ℤ := ∏ j, fBlk s (b j)

/-- Complex amplitudes of the unnormalised Shor codewords. -/
def cw (s : Bool) : Bas → ℂ := fun b => ((czw s b : ℤ) : ℂ)

/-- The normalisation constant `1 / (2 √2)`. -/
noncomputable def nrm : ℝ := 1 / (2 * Real.sqrt 2)

/-- The two (normalised) Shor codewords `|0_L⟩` and `|1_L⟩`, as amplitude functions on the
computational basis of nine qubits. -/
noncomputable def shorCodeword (s : Bool) : Bas → ℂ := fun b => (nrm : ℂ) * cw s b

lemma shorCodeword_eq (s : Bool) : shorCodeword s = fun b => (nrm : ℂ) * cw s b := rfl

/-! ## Inner product and Pauli operators -/

/-- The Hermitian inner product on the state space of nine qubits (conjugate-linear on the left). -/
noncomputable def ip (u v : Bas → ℂ) : ℂ := ∑ b : Bas, (starRingEnd ℂ) (u b) * v b

/-- The (phase-free) Pauli operator `∏ Z^{z} ∏ X^{x}` acting on amplitude functions. -/
def PauliOp (x z : Bas) (ψ : Bas → ℂ) : Bas → ℂ := fun b => (sgnb z b : ℂ) * ψ (bxorb x b)

/-- The per-block "transfer coefficient" of a Pauli operator between the block states. -/
def gBlk (s t : Bool) (u w : Blk) : ℤ :=
  ∑ β : Blk, fBlk s β * sgnB w β * fBlk t (bxorB u β)

/-! ## The core computation: matrix elements of Pauli operators between codewords -/

lemma czw_bxorb (t : Bool) (x b : Bas) : czw t (bxorb x b) = ∏ j, fBlk t (bxorB (x j) (b j)) := rfl

/-- Matrix elements of Pauli operators between the unnormalised codewords factor over the
three blocks. -/
lemma ip_cw_pauli_int (s t : Bool) (x z : Bas) :
    ∑ b : Bas, czw s b * sgnb z b * czw t (bxorb x b) = ∏ j, gBlk s t (x j) (z j) := by
  have h1 : (∏ j, gBlk s t (x j) (z j))
      = ∑ b ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset Blk)),
          ∏ j, (fBlk s (b j) * sgnB (z j) (b j) * fBlk t (bxorB (x j) (b j))) := by
    simpa [gBlk] using
      Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset Blk))
        (fun j β => fBlk s β * sgnB (z j) β * fBlk t (bxorB (x j) β))
  rw [h1, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [czw, sgnb, bxorb, ← Finset.prod_mul_distrib]

lemma ip_cw_pauli (s t : Bool) (x z : Bas) :
    ip (cw s) (PauliOp x z (cw t)) = ((∏ j, gBlk s t (x j) (z j) : ℤ) : ℂ) := by
  rw [← ip_cw_pauli_int]
  simp only [ip, PauliOp, cw]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_assoc]

/-! ## Weight of a Pauli operator -/

/-- Number of qubits of a block on which the Pauli operator `(u, w)` acts nontrivially. -/
def wtB (u w : Blk) : ℕ := ∑ k, if u k || w k then 1 else 0

/-- Number of qubits on which the Pauli operator `(x, z)` acts nontrivially. -/
def wt (x z : Bas) : ℕ := ∑ j, wtB (x j) (z j)

lemma wtB_oneB (w : Blk) : wtB oneB w = 3 := by revert w; decide

lemma wtB_pos_of_ne_zero (u w : Blk) (h : w ≠ zeroB) : 1 ≤ wtB u w := by
  revert u w; decide

lemma wtB_le_wt (x z : Bas) (j : Fin 3) : wtB (x j) (z j) ≤ wt x z :=
  Finset.single_le_sum (f := fun j => wtB (x j) (z j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)

/-! ## Block-level facts, verified by exhaustive computation -/

lemma gBlk_eq_zero_of_not_const (s t : Bool) (u w : Blk) (h : ¬ (u = zeroB ∨ u = oneB)) :
    gBlk s t u w = 0 := by
  revert s t u w; decide

lemma gBlk_diag (w : Blk) : gBlk false false zeroB w = gBlk true true zeroB w := by
  revert w; decide

lemma gBlk_offdiag_zero (s t : Bool) (h : s ≠ t) : gBlk s t zeroB zeroB = 0 := by
  revert s t; decide

/-! ## The Knill–Laflamme conditions for weight ≤ 2 Pauli operators -/

/-- For every Pauli operator of weight at most two, the diagonal matrix elements between the
two codewords agree and the off-diagonal matrix elements vanish.  This is exactly the
Knill–Laflamme condition, and it is the heart of the correctness of the Shor code. -/
theorem gBlk_prod_key (x z : Bas) (h : wt x z ≤ 2) (s t : Bool) :
    (∏ j, gBlk s t (x j) (z j))
      = if s = t then (∏ j, gBlk false false (x j) (z j)) else 0 := by
  by_cases hall : ∀ j, x j = zeroB
  · -- every `x j` is trivial
    by_cases hst : s = t
    · subst hst
      cases s with
      | false => simp
      | true =>
          rw [if_pos rfl]
          exact (Finset.prod_congr rfl fun j _ => by rw [hall j, ← gBlk_diag (z j)])
    · -- off-diagonal: some block carries no `z`, and there the coefficient vanishes
      have hz : ∃ j, z j = zeroB := by
        by_contra hc
        push_neg at hc
        have : 3 ≤ wt x z := by
          have : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 1 ≤ wtB (x j) (z j) :=
            fun j _ => wtB_pos_of_ne_zero _ _ (hc j)
          calc (3 : ℕ) = ∑ _j : Fin 3, 1 := by simp
            _ ≤ ∑ j : Fin 3, wtB (x j) (z j) := Finset.sum_le_sum this
            _ = wt x z := rfl
        omega
      obtain ⟨j, hj⟩ := hz
      rw [if_neg hst]
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [hall j, hj]
      exact gBlk_offdiag_zero s t hst
  · -- some `x j` is neither `000` nor `111`, so every product vanishes
    push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hj1 : x j ≠ oneB := by
      intro hc
      have := wtB_le_wt x z j
      rw [hc, wtB_oneB (z j)] at this
      omega
    have hnc : ¬ (x j = zeroB ∨ x j = oneB) := by
      rintro (h1 | h1) <;> [exact hj h1; exact hj1 h1]
    have hzero : ∀ s t : Bool, (∏ j, gBlk s t (x j) (z j)) = 0 := fun s t =>
      Finset.prod_eq_zero (Finset.mem_univ j) (gBlk_eq_zero_of_not_const s t _ _ hnc)
    rw [hzero s t, hzero false false]
    simp

/-! ## Bilinearity of the inner product -/

lemma ip_sum_left {ι : Type*} [Fintype ι] (f : ι → Bas → ℂ) (v : Bas → ℂ) :
    ip (fun b => ∑ i, f i b) v = ∑ i, ip (f i) v := by
  simp only [ip, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma ip_sum_right {ι : Type*} [Fintype ι] (u : Bas → ℂ) (g : ι → Bas → ℂ) :
    ip u (fun b => ∑ i, g i b) = ∑ i, ip u (g i) := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_comm

lemma ip_smul_left (k : ℂ) (u v : Bas → ℂ) :
    ip (fun b => k * u b) v = (starRingEnd ℂ) k * ip u v := by
  simp only [ip, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

lemma ip_smul_right (k : ℂ) (u v : Bas → ℂ) :
    ip u (fun b => k * v b) = k * ip u v := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ## Products of Pauli operators inside the inner product -/

/-- Adding a fixed bit-string is an involution, hence a permutation of the basis. -/
def xorEquiv (x : Bas) : Bas ≃ Bas :=
  Function.Involutive.toPerm (bxorb x) (bxorb_involutive x)

lemma ip_pauli_pauli (x z x' z' : Bas) (u v : Bas → ℂ) :
    ip (PauliOp x z u) (PauliOp x' z' v)
      = (sgnb (bxorb z z') x : ℂ) * ip u (PauliOp (bxorb x x') (bxorb z z') v) := by
  set w := bxorb z z' with hw
  set Φ : Bas → ℂ :=
    fun b => (sgnb w b : ℂ) * ((starRingEnd ℂ) (u (bxorb x b)) * v (bxorb x' b)) with hΦ
  have hL : ip (PauliOp x z u) (PauliOp x' z' v) = ∑ b : Bas, Φ b := by
    simp only [ip, PauliOp, hΦ]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hs : ((sgnb w b : ℤ) : ℂ) = ((sgnb z b : ℤ) : ℂ) * ((sgnb z' b : ℤ) : ℂ) := by
      rw [hw, ← sgnb_mul]; push_cast; ring
    rw [map_mul, hs]
    simp only [map_intCast]
    ring
  have hre : ∑ b : Bas, Φ b = ∑ b : Bas, Φ (bxorb x b) :=
    (Fintype.sum_equiv (xorEquiv x) (fun b => Φ (bxorb x b)) Φ (fun _ => rfl)).symm
  have hval : ∀ b : Bas, Φ (bxorb x b)
      = (sgnb w x : ℂ) * ((sgnb w b : ℂ) * ((starRingEnd ℂ) (u b) * v (bxorb (bxorb x x') b))) := by
    intro b
    have h1 : bxorb x (bxorb x b) = b := bxorb_involutive x b
    have h2 : bxorb x' (bxorb x b) = bxorb (bxorb x x') b := bxorb_left_comm x x' b
    have h3 : ((sgnb w (bxorb x b) : ℤ) : ℂ) = ((sgnb w x : ℤ) : ℂ) * ((sgnb w b : ℤ) : ℂ) := by
      rw [sgnb_xor_arg]; push_cast; ring
    simp only [hΦ, h1, h2, h3]
    ring
  rw [hL, hre]
  simp only [hval]
  rw [← Finset.mul_sum]
  congr 1
  simp only [ip, PauliOp]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ## Arbitrary single-qubit errors -/

/-- Change the value of the qubit `q` in the basis state `b` to `v`. -/
def upd (b : Bas) (q : Q) (v : Bool) : Bas :=
  Function.update b q.1 (Function.update (b q.1) q.2 v)

/-- An arbitrary operator `A` acting on the single qubit `q` (and as the identity on the other
eight qubits), written out on amplitude functions. -/
noncomputable def errOp (q : Q) (A : Bool → Bool → ℂ) (ψ : Bas → ℂ) : Bas → ℂ :=
  fun b => ∑ v : Bool, A (b q.1 q.2) v * ψ (upd b q v)

lemma upd_self (b : Bas) (q : Q) : upd b q (b q.1 q.2) = b := by
  simp [upd]

lemma upd_not (b : Bas) (q : Q) : upd b q (!(b q.1 q.2)) = bxorb (eQ q) b := by
  funext j k
  by_cases hj : j = q.1 <;> by_cases hk : k = q.2 <;>
    simp [upd, eQ, bxorb, bxorB, hj, hk]

/-- The Pauli support of a single-qubit operator: `bitP c q` is the indicator of `q` if `c`
is `true`, and trivial otherwise. -/
def bitP (c : Bool) (q : Q) : Bas := if c then eQ q else zeroBas

@[simp] lemma bitP_false (q : Q) : bitP false q = zeroBas := if_neg (by simp)

@[simp] lemma bitP_true (q : Q) : bitP true q = eQ q := if_pos rfl

lemma sgnb_eQ (q : Q) (b : Bas) : sgnb (eQ q) b = if b q.1 q.2 then -1 else 1 := by
  rw [sgnb, Finset.prod_eq_single q.1]
  · have : eQ q q.1 = eBlk q.2 := by
      funext k; simp [eQ, eBlk]
    rw [this, sgnB_eBlk]
  · intro j _ hj
    have : eQ q j = zeroB := by
      funext k; simp [eQ, zeroB, hj]
    rw [this, sgnB_zero]
  · intro h; exact absurd (Finset.mem_univ q.1) h

/-- The coefficients expressing a `2 × 2` matrix in the (phase-free) Pauli basis. -/
noncomputable def paCoef (A : Bool → Bool → ℂ) : Bool → Bool → ℂ
  | false, false => (A false false + A true true) / 2
  | false, true  => (A false false - A true true) / 2
  | true,  false => (A false true + A true false) / 2
  | true,  true  => (A false true - A true false) / 2

/-- Every single-qubit operator is a linear combination of the four Pauli operators supported
on that qubit. -/
lemma errOp_eq_pauli_comb (q : Q) (A : Bool → Bool → ℂ) (ψ : Bas → ℂ) :
    errOp q A ψ
      = fun b => ∑ xb : Bool, ∑ zb : Bool,
          paCoef A xb zb * PauliOp (bitP xb q) (bitP zb q) ψ b := by
  funext b
  have hz : PauliOp (bitP false q) (bitP false q) ψ b = ψ b := by
    simp [PauliOp]
  have hZ : PauliOp (bitP false q) (bitP true q) ψ b
      = (if b q.1 q.2 then (-1 : ℂ) else 1) * ψ b := by
    simp only [PauliOp, bitP_false, bitP_true, sgnb_eQ, bxorb_zero_left]
    split <;> norm_num
  have hX : PauliOp (bitP true q) (bitP false q) ψ b = ψ (bxorb (eQ q) b) := by
    simp [PauliOp]
  have hXZ : PauliOp (bitP true q) (bitP true q) ψ b
      = (if b q.1 q.2 then (-1 : ℂ) else 1) * ψ (bxorb (eQ q) b) := by
    simp only [PauliOp, bitP_true, sgnb_eQ]
    split <;> norm_num
  simp only [errOp, Fintype.sum_bool, hz, hZ, hX, hXZ, paCoef]
  cases hb : b q.1 q.2
  · have h1 : upd b q false = b := by rw [← hb]; exact upd_self b q
    have h2 : upd b q true = bxorb (eQ q) b := by
      have := upd_not b q; rw [hb] at this; simpa using this
    have hif : (if (false : Bool) = true then (-1 : ℂ) else 1) = 1 := by norm_num
    rw [h1, h2, hif]
    ring
  · have h1 : upd b q true = b := by rw [← hb]; exact upd_self b q
    have h2 : upd b q false = bxorb (eQ q) b := by
      have := upd_not b q; rw [hb] at this; simpa using this
    have hif : (if (true : Bool) = true then (-1 : ℂ) else 1) = -1 := by norm_num
    rw [h1, h2, hif]
    ring

/-! ## Errors on one or two qubits have weight at most two -/

lemma eQ_apply_ne (q p : Q) (h : p ≠ q) : eQ q p.1 p.2 = false := by
  by_cases h1 : p.1 = q.1
  · by_cases h2 : p.2 = q.2
    · exact absurd (Prod.ext_iff.mpr ⟨h1, h2⟩) h
    · simp [eQ, h2]
  · simp [eQ, h1]

lemma bitP_apply_ne (c : Bool) (q p : Q) (h : p ≠ q) : bitP c q p.1 p.2 = false := by
  cases c
  · simp [zeroBas, zeroB]
  · simpa using eQ_apply_ne q p h

lemma wt_eq_sum_Q (x z : Bas) : wt x z = ∑ p : Q, if x p.1 p.2 || z p.1 p.2 then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  rfl

lemma wt_le_two_of_supp (x z : Bas) (q q' : Q)
    (h : ∀ p : Q, p ≠ q → p ≠ q' → x p.1 p.2 = false ∧ z p.1 p.2 = false) :
    wt x z ≤ 2 := by
  rw [wt_eq_sum_Q]
  have hsub : ∑ p ∈ ({q, q'} : Finset Q), (if x p.1 p.2 || z p.1 p.2 then 1 else 0)
      = ∑ p : Q, (if x p.1 p.2 || z p.1 p.2 then 1 else 0) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    obtain ⟨h1, h2⟩ := h p hp.1 hp.2
    simp [h1, h2]
  rw [← hsub]
  calc ∑ p ∈ ({q, q'} : Finset Q), (if x p.1 p.2 || z p.1 p.2 then 1 else 0)
      ≤ ∑ _p ∈ ({q, q'} : Finset Q), 1 := Finset.sum_le_sum fun p _ => by split <;> simp
    _ = ({q, q'} : Finset Q).card := by simp
    _ ≤ 2 := by simpa using Finset.card_insert_le q ({q'} : Finset Q)

lemma wt_bitP_le_two (xb zb xb' zb' : Bool) (q q' : Q) :
    wt (bxorb (bitP xb q) (bitP xb' q')) (bxorb (bitP zb q) (bitP zb' q')) ≤ 2 := by
  refine wt_le_two_of_supp _ _ q q' fun p hp hp' => ?_
  constructor <;>
    simp [bxorb, bxorB, bitP_apply_ne _ _ _ hp, bitP_apply_ne _ _ _ hp']

/-! ## Knill–Laflamme for pairs of Pauli operators of small support -/

lemma ip_pauli_cw (X Z X' Z' : Bas) (h : wt (bxorb X X') (bxorb Z Z') ≤ 2) (s t : Bool) :
    ip (PauliOp X Z (cw s)) (PauliOp X' Z' (cw t))
      = if s = t then ip (PauliOp X Z (cw false)) (PauliOp X' Z' (cw false)) else 0 := by
  rw [ip_pauli_pauli, ip_pauli_pauli, ip_cw_pauli, ip_cw_pauli,
    gBlk_prod_key _ _ h s t, gBlk_prod_key _ _ h false false]
  by_cases hst : s = t
  · simp only [if_pos hst]
  · simp only [if_neg hst, Int.cast_zero, mul_zero]

/-! ## Additivity lemmas -/

lemma ip_add_left (u₁ u₂ v : Bas → ℂ) :
    ip (fun b => u₁ b + u₂ b) v = ip u₁ v + ip u₂ v := by
  simp only [ip, map_add, add_mul, Finset.sum_add_distrib]

lemma ip_add_right (u v₁ v₂ : Bas → ℂ) :
    ip u (fun b => v₁ b + v₂ b) = ip u v₁ + ip u v₂ := by
  simp only [ip, mul_add, Finset.sum_add_distrib]

/-! ## Knill–Laflamme for arbitrary single-qubit errors -/

lemma ip_err_err_cw (q q' : Q) (A A' : Bool → Bool → ℂ) (s t : Bool) :
    ip (errOp q A (cw s)) (errOp q' A' (cw t))
      = if s = t then ip (errOp q A (cw false)) (errOp q' A' (cw false)) else 0 := by
  have hexp : ∀ r r' : Bool, ip (errOp q A (cw r)) (errOp q' A' (cw r'))
      = ∑ xb : Bool, ∑ zb : Bool, ∑ xb' : Bool, ∑ zb' : Bool,
          (starRingEnd ℂ) (paCoef A xb zb) * (paCoef A' xb' zb' *
            ip (PauliOp (bitP xb q) (bitP zb q) (cw r))
               (PauliOp (bitP xb' q') (bitP zb' q') (cw r'))) := by
    intro r r'
    rw [errOp_eq_pauli_comb, errOp_eq_pauli_comb]
    simp only [Fintype.sum_bool, ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]
    ring
  rw [hexp s t]
  by_cases hst : s = t
  · rw [if_pos hst, hexp false false]
    refine Finset.sum_congr rfl fun xb _ => Finset.sum_congr rfl fun zb _ =>
      Finset.sum_congr rfl fun xb' _ => Finset.sum_congr rfl fun zb' _ => ?_
    rw [ip_pauli_cw _ _ _ _ (wt_bitP_le_two xb zb xb' zb' q q') s t, if_pos hst]
  · rw [if_neg hst]
    refine Finset.sum_eq_zero fun xb _ => Finset.sum_eq_zero fun zb _ =>
      Finset.sum_eq_zero fun xb' _ => Finset.sum_eq_zero fun zb' _ => ?_
    rw [ip_pauli_cw _ _ _ _ (wt_bitP_le_two xb zb xb' zb' q q') s t, if_neg hst]
    ring

/-! ## Normalisation -/

lemma gBlk_zz (s t : Bool) : gBlk s t zeroB zeroB = if s = t then 2 else 0 := by
  revert s t; decide

lemma ip_cw_cw (s t : Bool) : ip (cw s) (cw t) = if s = t then 8 else 0 := by
  have h : PauliOp zeroBas zeroBas (cw t) = cw t := by
    funext b; simp [PauliOp]
  rw [← h, ip_cw_pauli]
  have hj : ∀ j : Fin 3, gBlk s t (zeroBas j) (zeroBas j) = gBlk s t zeroB zeroB := fun _ => rfl
  simp only [hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin, gBlk_zz]
  cases s <;> cases t <;> norm_num

lemma nrm_mul_nrm : nrm * nrm = 1 / 8 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [nrm]
  field_simp
  nlinarith [h2]

lemma errOp_smul (q : Q) (A : Bool → Bool → ℂ) (k : ℂ) (ψ : Bas → ℂ) :
    errOp q A (fun b => k * ψ b) = fun b => k * errOp q A ψ b := by
  funext b
  simp only [errOp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-! ## Main theorem -/

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

The two logical states `|0_L⟩`, `|1_L⟩` (`shorCodeword false`, `shorCodeword true`) are
orthonormal, and for *any* two single-qubit operators `A` at qubit `q` and `A'` at qubit `q'`
(these span all errors acting on a single, arbitrary, unknown qubit) the Knill–Laflamme
error-correction conditions hold:
`⟨i_L| E† F |j_L⟩ = α δ_{ij}` with a constant `α` depending only on the errors, not on the
encoded state.  By the Knill–Laflamme theorem this is exactly the statement that the code
corrects the corresponding error set, i.e. an arbitrary error on one qubit. -/
theorem shor_code_corrects :
    (∀ s t : Bool, ip (shorCodeword s) (shorCodeword t) = if s = t then 1 else 0) ∧
    (∀ (q q' : Q) (A A' : Bool → Bool → ℂ), ∃ α : ℂ, ∀ s t : Bool,
      ip (errOp q A (shorCodeword s)) (errOp q' A' (shorCodeword t))
        = if s = t then α else 0) := by
  have hcast : ((nrm : ℂ)) * (nrm : ℂ) = 1 / 8 := by
    have := nrm_mul_nrm
    have : ((nrm * nrm : ℝ) : ℂ) = ((1 / 8 : ℝ) : ℂ) := by rw [this]
    push_cast at this
    simpa using this
  constructor
  · intro s t
    have : ip (shorCodeword s) (shorCodeword t) = (nrm : ℂ) * ((nrm : ℂ) * ip (cw s) (cw t)) := by
      simp only [shorCodeword_eq, ip_smul_left, ip_smul_right, Complex.conj_ofReal]
    rw [this, ip_cw_cw]
    cases s <;> cases t <;> simp <;> · rw [← mul_assoc, hcast]; norm_num
  · intro q q' A A'
    refine ⟨(nrm : ℂ) * ((nrm : ℂ) * ip (errOp q A (cw false)) (errOp q' A' (cw false))), ?_⟩
    intro s t
    have hs : ip (errOp q A (shorCodeword s)) (errOp q' A' (shorCodeword t))
        = (nrm : ℂ) * ((nrm : ℂ) * ip (errOp q A (cw s)) (errOp q' A' (cw t))) := by
      simp only [shorCodeword_eq, errOp_smul, ip_smul_left, ip_smul_right, Complex.conj_ofReal]
    rw [hs, ip_err_err_cw]
    by_cases hst : s = t
    · rw [if_pos hst, if_pos hst]
    · rw [if_neg hst, if_neg hst, mul_zero, mul_zero]

/-! ## Sanity checks: the statement has real content -/

/-- The identity error is in the error set: taking `A` to be the identity matrix on the qubit
`q` gives back the state unchanged. -/
lemma errOp_id (q : Q) (ψ : Bas → ℂ) :
    errOp q (fun u v => if u = v then 1 else 0) ψ = ψ := by
  funext b
  have h : upd b q (b q.1 q.2) = b := upd_self b q
  simp only [errOp, Fintype.sum_bool]
  cases hb : b q.1 q.2 <;> rw [hb] at h <;> simp [h]

/-- The restriction to *single*-qubit errors is essential: the weight-three Pauli operator
consisting of one `Z` in each block (the logical `X` of the Shor code) maps `|1_L⟩` to a state
with a nonzero overlap with `|0_L⟩`, so it violates the Knill–Laflamme condition. -/
lemma logicalX_violates_KL :
    wt zeroBas (fun _ => eBlk 0) = 3 ∧
      ip (cw false) (PauliOp zeroBas (fun _ => eBlk 0) (cw true)) ≠ 0 := by
  refine ⟨by decide, ?_⟩
  rw [ip_cw_pauli]
  have h : (∏ j : Fin 3, gBlk false true (zeroBas j) ((fun _ : Fin 3 => eBlk 0) j)) = 8 := by
    decide
  rw [h]
  norm_num

end QI

