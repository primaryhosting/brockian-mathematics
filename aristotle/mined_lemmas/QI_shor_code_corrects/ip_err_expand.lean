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
