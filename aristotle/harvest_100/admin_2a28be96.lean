import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the statement that the nine–qubit Shor code corrects an arbitrary
single–qubit error, in the form of the Knill–Laflamme error–correction conditions.

* The nine qubits are grouped into three blocks of three: a computational basis
  state is a function `Cfg = Fin 3 → Blk` with `Blk = Bool × Bool × Bool`.
* The two logical codewords are
  `|0_L⟩ = ((|000⟩+|111⟩)/√2)^{⊗3}` and `|1_L⟩ = ((|000⟩-|111⟩)/√2)^{⊗3}`.
* A Pauli operator `P a b` acts by `|x⟩ ↦ (-1)^{b·x} |x ⊕ a⟩`; taking `a`, `b`
  supported on a single qubit `q` gives the four operators `I, X_q, Z_q, X_q Z_q`,
  which span all operators acting on qubit `q` alone (since `Y_q = i X_q Z_q`).
  A general single–qubit error on `q` is therefore `err q g` for an arbitrary
  coefficient vector `g : Bool × Bool → ℂ`.
* The Knill–Laflamme condition `⟨i_L| E† F |j_L⟩ = c(E,F) δ_{ij}` is stated as
  `ip (err q g (cw i)) (err r h (cw j)) = if i = j then c else 0`, using
  `⟨i|E†F|j⟩ = ⟨E i, F j⟩`.
-/

namespace QI

/-! ### Basic combinatorial set-up -/

/-- A block of three qubits. -/
abbrev Blk := Bool × Bool × Bool

/-- A computational basis configuration of the nine qubits (three blocks of three). -/
abbrev Cfg := Fin 3 → Blk

/-- The all-zero block. -/
def zb : Blk := (false, false, false)

/-- The all-one block. -/
def ob : Blk := (true, true, true)

/-- Bitwise xor on a block. -/
def xb (w a : Blk) : Blk := (xor w.1 a.1, xor w.2.1 a.2.1, xor w.2.2 a.2.2)

/-- Parity of the bitwise `and` of two blocks. -/
def pb (b w : Blk) : Bool := xor (xor (b.1 && w.1) (b.2.1 && w.2.1)) (b.2.2 && w.2.2)

/-- `sgn t = (-1)^t`. -/
def sgn (t : Bool) : ℤ := if t then -1 else 1

/-- Bitwise xor on configurations. -/
def xorC (x a : Cfg) : Cfg := fun m => xb (x m) (a m)

/-- Parity of the bitwise `and` of two configurations. -/
def parC (b x : Cfg) : Bool :=
  xor (xor (pb (b 0) (x 0)) (pb (b 1) (x 1))) (pb (b 2) (x 2))

/-- The all-zero configuration. -/
def zC : Cfg := fun _ => zb

/-! ### Codewords -/

/-- The (unnormalised, integer) amplitude of a single block in `(|000⟩ ± |111⟩)`. -/
def blk (s : Bool) (w : Blk) : ℤ :=
  if w = zb then 1 else if w = ob then (if s then -1 else 1) else 0

/-- Unnormalised integer amplitudes of the logical codewords. -/
def cwZ (s : Bool) (x : Cfg) : ℤ := ∏ m, blk s (x m)

/-- The normalisation constant `1/(2√2)`. -/
noncomputable def kap : ℝ := (Real.sqrt 8)⁻¹

/-- The logical codewords of the Shor code: `cw false = |0_L⟩`, `cw true = |1_L⟩`. -/
noncomputable def cw (s : Bool) : Cfg → ℂ := fun x => (kap : ℂ) * (cwZ s x : ℂ)

/-! ### Operators -/

/-- The Pauli operator sending `|x⟩` to `(-1)^{b·x}|x ⊕ a⟩`. -/
noncomputable def pauli (a b : Cfg) (v : Cfg → ℂ) : Cfg → ℂ :=
  fun y => (sgn (parC b (xorC y a)) : ℂ) * v (xorC y a)

/-- The Hermitian inner product on the nine-qubit state space. -/
noncomputable def ip (v w : Cfg → ℂ) : ℂ := ∑ x : Cfg, (starRingEnd ℂ) (v x) * w x

/-- Indicator block for position `n`. -/
def delB (n : Fin 3) : Blk := (decide (n = 0), decide (n = 1), decide (n = 2))

/-- The `X`-part of the `k`-th Pauli supported on qubit `q = (block, position)`. -/
def aOf (q : Fin 3 × Fin 3) (k : Bool × Bool) : Cfg :=
  fun m => if k.1 = true ∧ m = q.1 then delB q.2 else zb

/-- The `Z`-part of the `k`-th Pauli supported on qubit `q = (block, position)`. -/
def bOf (q : Fin 3 × Fin 3) (k : Bool × Bool) : Cfg :=
  fun m => if k.2 = true ∧ m = q.1 then delB q.2 else zb

/-- An arbitrary linear operator acting on qubit `q` alone: a linear combination
of `I`, `X_q`, `Z_q`, `X_q Z_q` (which span the four-dimensional space of
single-qubit operators, since `Y_q = i X_q Z_q`). -/
noncomputable def err (q : Fin 3 × Fin 3) (g : Bool × Bool → ℂ) (v : Cfg → ℂ) : Cfg → ℂ :=
  fun y => ∑ k : Bool × Bool, g k * pauli (aOf q k) (bOf q k) v y

/-! ### The block transfer sums -/

/-- Summand of the per-block transfer sum. -/
def tb (i j : Bool) (bm b'm Am w : Blk) : ℤ :=
  sgn (pb bm w) * sgn (pb b'm (xb w Am)) * blk i w * blk j (xb w Am)

/-- Per-block transfer sum. -/
def T (i j : Bool) (bm b'm Am : Blk) : ℤ := ∑ w : Blk, tb i j bm b'm Am w

/-! ### Finite verifications -/

set_option maxRecDepth 10000 in
/-- Key finite check: as long as the `X`-part of the block is not the all-one
block, the diagonal transfer sums for the two codewords agree. -/
theorem T_diag_eq (bm b'm Am : Blk) (h : Am ≠ ob) :
    T true true bm b'm Am = T false false bm b'm Am := by
  revert bm b'm Am; decide

/-- On an untouched block the transfer sum vanishes off the diagonal. -/
theorem T_untouched (i j : Bool) (h : i ≠ j) : T i j zb zb zb = 0 := by
  revert i j; decide

theorem T_untouched_diag (i : Bool) : T i i zb zb zb = 2 := by revert i; decide

theorem xb_zb (w : Blk) : xb w zb = w := by revert w; decide

theorem xb_involutive (w a : Blk) : xb (xb w a) a = w := by revert w a; decide

theorem xb_assoc (u v w : Blk) : xb (xb u v) w = xb u (xb v w) := by revert u v w; decide

theorem xb_cancel (u v : Blk) : xb u (xb u v) = v := by revert u v; decide

theorem xb_zb_zb : xb zb zb = zb := by decide

theorem sgn_xor (s t : Bool) : sgn (xor s t) = sgn s * sgn t := by revert s t; decide

theorem delB_xor_ne_ob (t1 t2 : Bool) (n n' : Fin 3) :
    xb (if t1 then delB n else zb) (if t2 then delB n' else zb) ≠ ob := by
  revert t1 t2 n n'; decide

/-! ### Configuration-level lemmas -/

theorem xorC_involutive (z a : Cfg) : xorC (xorC z a) a = z := by
  funext m; simp [xorC, xb_involutive]

theorem xorC_assoc (u v w : Cfg) : xorC (xorC u v) w = xorC u (xorC v w) := by
  funext m; simp [xorC, xb_assoc]

theorem xorC_cancel (u v : Cfg) : xorC u (xorC u v) = v := by
  funext m; simp [xorC, xb_cancel]

theorem pauli_zero (v : Cfg → ℂ) : pauli zC zC v = v := by
  funext y
  have h1 : xorC y zC = y := by funext m; simp [xorC, zC, xb_zb]
  simp [pauli, h1, parC, zC, pb, zb, sgn]

/-! ### Core computation -/

/-- The integer core of the inner product of two Pauli-rotated codewords. -/
def Zs (i j : Bool) (a b a' b' : Cfg) : ℤ :=
  ∑ y : Cfg, sgn (parC b (xorC y a)) * sgn (parC b' (xorC y a'))
      * cwZ i (xorC y a) * cwZ j (xorC y a')

theorem ip_pauli_eq (i j : Bool) (a b a' b' : Cfg) :
    ip (pauli a b (cw i)) (pauli a' b' (cw j)) = (kap : ℂ) ^ 2 * (Zs i j a b a' b' : ℂ) := by
  unfold ip pauli cw Zs
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [map_mul, Complex.conj_ofReal, map_intCast]
  ring

theorem Zs_reindex (i j : Bool) (a b a' b' : Cfg) :
    Zs i j a b a' b' =
      ∑ z : Cfg, sgn (parC b z) * sgn (parC b' (xorC z (xorC a a')))
        * cwZ i z * cwZ j (xorC z (xorC a a')) := by
  unfold Zs
  refine Fintype.sum_equiv
    ⟨fun z => xorC z a, fun z => xorC z a, fun z => xorC_involutive z a,
      fun z => xorC_involutive z a⟩ _ _ ?_
  intro y
  have h1 : xorC (xorC y a) (xorC a a') = xorC y a' := by
    rw [xorC_assoc, xorC_cancel]
  simp only [Equiv.coe_fn_mk, h1]

theorem sum_factor (i j : Bool) (b b' A : Cfg) :
    (∑ z : Cfg, sgn (parC b z) * sgn (parC b' (xorC z A)) * cwZ i z * cwZ j (xorC z A))
      = ∏ m, T i j (b m) (b' m) (A m) := by
  have hT : (∏ m, T i j (b m) (b' m) (A m))
      = ∏ m : Fin 3, ∑ w ∈ (Finset.univ : Finset Blk), tb i j (b m) (b' m) (A m) w := rfl
  rw [hT, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [parC, sgn_xor, cwZ, tb, xorC, Fin.prod_univ_three]
  ring

/-- Master formula: the inner product factorises over the three blocks. -/
theorem ip_pauli_formula (i j : Bool) (a b a' b' : Cfg) :
    ip (pauli a b (cw i)) (pauli a' b' (cw j))
      = (kap : ℂ) ^ 2 * ((∏ m, T i j (b m) (b' m) ((xorC a a') m) : ℤ) : ℂ) := by
  rw [ip_pauli_eq, Zs_reindex, sum_factor]

theorem kap_sq : (kap : ℂ) ^ 2 = 1 / 8 := by
  have h : (kap : ℝ) ^ 2 = 1 / 8 := by
    rw [kap, inv_pow, Real.sq_sqrt (by norm_num : (8:ℝ) ≥ 0)]
    norm_num
  have := congrArg (fun t : ℝ => (t : ℂ)) h
  push_cast at this
  exact this

/-! ### Orthonormality of the codewords -/

theorem cw_orthonormal (i j : Bool) : ip (cw i) (cw j) = if i = j then 1 else 0 := by
  have h : ip (cw i) (cw j) = ip (pauli zC zC (cw i)) (pauli zC zC (cw j)) := by
    rw [pauli_zero, pauli_zero]
  rw [h, ip_pauli_formula, kap_sq]
  have hz : xorC zC zC = zC := by funext m; simp [xorC, zC, xb, zb]
  rw [hz]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have : ∀ m : Fin 3, T i i ((zC : Cfg) m) ((zC : Cfg) m) ((zC : Cfg) m) = 2 := by
      intro m; simpa [zC] using T_untouched_diag i
    rw [Finset.prod_congr rfl (fun m _ => this m)]
    norm_num
  · rw [if_neg hij]
    have : T i j ((zC : Cfg) 0) ((zC : Cfg) 0) ((zC : Cfg) 0) = 0 := by
      simpa [zC] using T_untouched i j hij
    rw [Fin.prod_univ_three]
    rw [this]
    simp

/-! ### Knill–Laflamme for a pair of single-qubit Paulis -/

theorem exists_untouched_block (q r : Fin 3 × Fin 3) :
    ∃ m : Fin 3, m ≠ q.1 ∧ m ≠ r.1 := by
  revert q r; decide

theorem A_ne_ob (q r : Fin 3 × Fin 3) (k l : Bool × Bool) (m : Fin 3) :
    (xorC (aOf q k) (aOf r l)) m ≠ ob := by
  show xb (aOf q k m) (aOf r l m) ≠ ob
  have h1 : aOf q k m = if (k.1 && decide (m = q.1)) = true then delB q.2 else zb := by
    by_cases hk : k.1 = true <;> by_cases hm : m = q.1 <;> simp [aOf, hk, hm]
  have h2 : aOf r l m = if (l.1 && decide (m = r.1)) = true then delB r.2 else zb := by
    by_cases hl : l.1 = true <;> by_cases hm : m = r.1 <;> simp [aOf, hl, hm]
  rw [h1, h2]
  exact delB_xor_ne_ob _ _ _ _

theorem pauli_KL (q r : Fin 3 × Fin 3) (k l : Bool × Bool) (i j : Bool) :
    ip (pauli (aOf q k) (bOf q k) (cw i)) (pauli (aOf r l) (bOf r l) (cw j))
      = if i = j then
          ip (pauli (aOf q k) (bOf q k) (cw false)) (pauli (aOf r l) (bOf r l) (cw false))
        else 0 := by
  rw [ip_pauli_formula, ip_pauli_formula]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    cases i with
    | false => rfl
    | true =>
        have hprod : (∏ m, T true true (bOf q k m) (bOf r l m) (xorC (aOf q k) (aOf r l) m))
            = ∏ m, T false false (bOf q k m) (bOf r l m) (xorC (aOf q k) (aOf r l) m) :=
          Finset.prod_congr rfl fun m _ => T_diag_eq _ _ _ (A_ne_ob q r k l m)
        rw [hprod]
  · rw [if_neg hij]
    obtain ⟨m, hm1, hm2⟩ := exists_untouched_block q r
    have hb : bOf q k m = zb := by simp [bOf, hm1]
    have hb' : bOf r l m = zb := by simp [bOf, hm2]
    have ha : aOf q k m = zb := by simp [aOf, hm1]
    have ha' : aOf r l m = zb := by simp [aOf, hm2]
    have hA : (xorC (aOf q k) (aOf r l)) m = zb := by
      show xb (aOf q k m) (aOf r l m) = zb
      rw [ha, ha', xb_zb_zb]
    have hzero : (∏ m, T i j (bOf q k m) (bOf r l m) ((xorC (aOf q k) (aOf r l)) m)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ m)
        (by rw [hb, hb', hA]; exact T_untouched i j hij)
    rw [hzero]
    simp

/-! ### Bilinear expansion -/

theorem ip_err_expand (q r : Fin 3 × Fin 3) (g h : Bool × Bool → ℂ) (v w : Cfg → ℂ) :
    ip (err q g v) (err r h w)
      = ∑ k : Bool × Bool, ∑ l : Bool × Bool,
          (starRingEnd ℂ) (g k) * h l *
            ip (pauli (aOf q k) (bOf q k) v) (pauli (aOf r l) (bOf r l) w) := by
  have hx : ∀ x : Cfg, (starRingEnd ℂ) (err q g v x) * err r h w x
      = ∑ k : Bool × Bool, ∑ l : Bool × Bool, (starRingEnd ℂ) (g k) * h l *
          ((starRingEnd ℂ) (pauli (aOf q k) (bOf q k) v x) * pauli (aOf r l) (bOf r l) w x) := by
    intro x
    simp only [err, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [ip, hx]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]

/-! ### Main theorem -/

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

The first conjunct says that the two logical codewords `|0_L⟩`, `|1_L⟩` are
orthonormal, so they span a genuine two-dimensional code space.

The second conjunct is the Knill–Laflamme error-correction condition for the set
of all single-qubit errors: for any two qubits `q`, `r` and any single-qubit
operators `E = err q g` on `q` and `F = err r h` on `r`, there is a scalar `c`
(depending only on `E` and `F`) with `⟨i_L| E† F |j_L⟩ = c · δ_{ij}`.  Since
`I`, `X`, `Z`, `XZ` span all one-qubit operators, this covers arbitrary
single-qubit errors, and by the Knill–Laflamme theorem it is exactly the
condition for the code to correct them. -/
theorem shor_code_corrects :
    (∀ i j : Bool, ip (cw i) (cw j) = if i = j then 1 else 0) ∧
    (∀ (q r : Fin 3 × Fin 3) (g h : Bool × Bool → ℂ), ∃ c : ℂ, ∀ i j : Bool,
        ip (err q g (cw i)) (err r h (cw j)) = if i = j then c else 0) := by
  refine ⟨cw_orthonormal, ?_⟩
  intro q r g h
  refine ⟨∑ k : Bool × Bool, ∑ l : Bool × Bool, (starRingEnd ℂ) (g k) * h l *
      ip (pauli (aOf q k) (bOf q k) (cw false)) (pauli (aOf r l) (bOf r l) (cw false)), ?_⟩
  intro i j
  rw [ip_err_expand]
  by_cases hij : i = j
  · rw [if_pos hij]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [pauli_KL, if_pos hij]
  · rw [if_neg hij]
    have : ∀ k : Bool × Bool, ∀ l : Bool × Bool,
        (starRingEnd ℂ) (g k) * h l *
          ip (pauli (aOf q k) (bOf q k) (cw i)) (pauli (aOf r l) (bOf r l) (cw j)) = 0 := by
      intro k l; rw [pauli_KL, if_neg hij, mul_zero]
    simp [this]

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

