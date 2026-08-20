import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem four_mul_choose_le (n i D : ℕ) (h : 32 * D ^ 2 ≤ n + 1) :
    4 * D * (n.choose i) ≤ 2 ^ n := by
  have hb := choose_sq_mul_succ_le n i
  have key : (4 * D * (n.choose i)) ^ 2 * (n + 1) ≤ (2 ^ n) ^ 2 * (n + 1) := by
    calc (4 * D * (n.choose i)) ^ 2 * (n + 1)
        = 16 * D ^ 2 * ((n.choose i) ^ 2 * (n + 1)) := by ring
      _ ≤ 16 * D ^ 2 * (2 * 4 ^ n) := Nat.mul_le_mul_left _ hb
      _ = (32 * D ^ 2) * 4 ^ n := by ring
      _ ≤ (n + 1) * 4 ^ n := Nat.mul_le_mul_right _ h
      _ = (2 ^ n) ^ 2 * (n + 1) := by
          rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]; ring
  have h2 : (4 * D * (n.choose i)) ^ 2 ≤ (2 ^ n) ^ 2 :=
    Nat.le_of_mul_le_mul_right key (by omega)
  exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).1 h2

end CS

import Mathlib

/-!
Constant depth circuits with unbounded fan-in AND / OR / NOT gates and `MOD q` gates,
i.e. the class `AC⁰[q]`.

A circuit is a directed acyclic graph, encoded by listing its gates in topological order:
gate number `i` may only refer to gates with a strictly smaller index.
-/

namespace CS

open Finset

/-- A gate whose children are among the gates with index `< k`. -/
inductive GateSpec (n : ℕ) (k : ℕ) where
  /-- the `i`-th input variable -/
  | inp : Fin n → GateSpec n k
  /-- a constant -/
  | cst : Bool → GateSpec n k
  /-- negation of gate `j` -/
  | notg : Fin k → GateSpec n k
  /-- unbounded fan-in OR of a set of gates -/
  | org : Finset (Fin k) → GateSpec n k
  /-- unbounded fan-in AND of a set of gates -/
  | andg : Finset (Fin k) → GateSpec n k
  /-- `MOD q` gate: outputs `true` iff the number of `true` inputs (with multiplicity,
  hence a list) is not divisible by `q` -/
  | modg : List (Fin k) → GateSpec n k

/-- A circuit on `n` Boolean inputs. -/
structure Circuit (n : ℕ) where
  /-- number of gates -/
  size : ℕ
  /-- the specification of each gate; children have smaller indices -/
  gate : (i : Fin size) → GateSpec n i.val
  /-- the output gate -/
  out : Fin size

namespace Circuit

variable {n : ℕ}

/-- View a child index of gate `i` as a gate index. -/
