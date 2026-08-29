import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

We work with 7 qubits.  The computational basis of the state space is indexed by
`V2 = Fin 7 → ZMod 2` (bit strings of length 7), and a state is a function `Ket = V2 → ℂ`.

For `a b : V2` the Pauli operator `pauli a b` acts on basis kets by
`P(a,b) |v⟩ = (-1)^(b ⬝ v) |v + a⟩`; thus `pauli a 0` is a product of `X`'s on the support of
`a`, `pauli 0 b` a product of `Z`'s on the support of `b`, and `pauli a b` with `a = b`
supported on one qubit is `Y` on that qubit (up to the irrelevant global phase `i`).

The Steane code is the CSS code built from the `[7,4,3]` Hamming code: the two logical basis
states `u 0`, `u 1` are the uniform superpositions over the two cosets of the dual Hamming
code `C₂` (the `[7,3,4]` simplex code) inside the Hamming code.

The theorem `QI.steane_code` states the Knill–Laflamme error-correction conditions for the
set of *all* single-qubit Pauli errors, together with the fact that the two logical basis
states are orthogonal and nonzero (so the code space really is two-dimensional).
Since `⟪E u_i, F u_j⟫ = ⟪u_i, E† F u_j⟫`, the second conjunct is literally the
Knill–Laflamme condition `P E† F P = c_{E,F} · P` for the projector `P` onto the code space,
which is necessary and sufficient for the existence of a recovery channel correcting every
single-qubit error.
-/

/-- Bit strings of length 7 (indices of the computational basis of 7 qubits). -/
abbrev V2 := Fin 7 → ZMod 2

/-- A state of the 7 qubits, given by its computational-basis amplitudes. -/
abbrev Ket := V2 → ℂ

/-- The sign character `(-1) ^ x` of `ZMod 2`, valued in `ℂ`. -/

lemma inner_diag {a b a' b' : V2} (hp : Wt2 (a + a')) (i : Fin 2) :
    inner' (pauli a b (u i)) (pauli a' b' (u i))
      = if a = a' then eps (dot (b + b') (shift i)) * ∑ c ∈ C2, eps (dot (b + b') c) else 0 := by
  rw [inner_pauli]
  by_cases hpz : a + a' = 0
  · have haa : a = a' := by
      have := congrArg (· + a') hpz
      simpa [add_cancel_v2] using this
    subst haa
    have hz : a + a = (0 : V2) := add_self_v2 a
    rw [hz]
    have hterm : ∀ c ∈ C2, eps (dot (b + b') (c + shift i)) * u i (c + shift i + 0)
        = eps (dot (b + b') (shift i)) * eps (dot (b + b') c) := by
      intro c hc
      have hmem : c + shift i + 0 ∈ code i := by
        rw [mem_code_iff, add_zero, add_cancel_v2]
        exact hc
      unfold u
      rw [if_pos hmem, mul_one, dot_add_right, eps_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    simp [dot_zero_right, eps_zero]
  · have hne : a ≠ a' := by
      intro h; apply hpz; rw [h]; exact add_self_v2 a'
    have hterm : ∀ c ∈ C2, eps (dot (b + b') (c + shift i)) * u i (c + shift i + (a + a')) = 0 := by
      intro c hc
      have hnot : c + shift i + (a + a') ∉ code i := by
        rw [mem_code_iff]
        intro hmem
        have hst : shift i + shift i = (0 : V2) := add_self_v2 _
        have hre : c + shift i + (a + a') + shift i = c + ((a + a') + (shift i + shift i)) := by
          abel
        rw [hre, hst, add_zero, C2_add_iff hc] at hmem
        exact hpz (C2_min_weight _ hmem hp)
      unfold u
      simp [hnot]
    rw [Finset.sum_congr rfl hterm]
    simp [hne]

/-- Every single-qubit Pauli operator on qubit `q` (namely `I`, `X`, `Z` and, up to a global
phase, `Y`, according to the values of `x` and `z`) belongs to the error set. -/
