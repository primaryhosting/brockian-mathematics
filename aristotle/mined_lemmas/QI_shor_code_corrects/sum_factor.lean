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
