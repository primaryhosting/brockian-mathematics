/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma tp_update_conj {n : ℕ} (q : Fin n) (A : Matrix (ZMod 2) (ZMod 2) ℂ)
    (P P' : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) (v : ℂ)
    (hq : A * P q = v • (P' q * A)) (hne : ∀ r, r ≠ q → P' r = P r) :
    tp (Function.update (fun _ => 1) q A) * tp P
      = v • (tp P' * tp (Function.update (fun _ => 1) q A)) := by
  have h := tp_conj (Function.update (fun _ => 1) q A) P P'
    (Function.update (fun _ : Fin n => (1 : ℂ)) q v) ?_
  · rwa [prod_update_one] at h
  · intro r
    by_cases hr : r = q
    · subst hr; simpa using hq
    · simp [Function.update_of_ne hr, hne r hr]

/-! ## Paulis, gates and the tableau update -/

/-- A Pauli operator on `n` qubits in tableau form: a phase in `ZMod 4` together with
the `X`-exponents and `Z`-exponents. -/
structure Pauli (n : ℕ) where
  /-- The power of `i` in front. -/
  s : ZMod 4
  /-- The `X` exponents. -/
  x : Fin n → ZMod 2
  /-- The `Z` exponents. -/
  z : Fin n → ZMod 2

/-- The `2^n × 2^n` matrix of a Pauli operator. -/
