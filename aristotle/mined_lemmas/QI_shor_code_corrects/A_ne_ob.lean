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

theorem A_ne_ob (q r : Fin 3 × Fin 3) (k l : Bool × Bool) (m : Fin 3) :
    (xorC (aOf q k) (aOf r l)) m ≠ ob := by
  show xb (aOf q k m) (aOf r l m) ≠ ob
  have h1 : aOf q k m = if (k.1 && decide (m = q.1)) = true then delB q.2 else zb := by
    by_cases hk : k.1 = true <;> by_cases hm : m = q.1 <;> simp [aOf, hk, hm]
  have h2 : aOf r l m = if (l.1 && decide (m = r.1)) = true then delB r.2 else zb := by
    by_cases hl : l.1 = true <;> by_cases hm : m = r.1 <;> simp [aOf, hl, hm]
  rw [h1, h2]
  exact delB_xor_ne_ob _ _ _ _

