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

