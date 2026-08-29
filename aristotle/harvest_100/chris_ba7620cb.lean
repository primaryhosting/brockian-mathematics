import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational basis labels for three qubits. -/
abbrev Three := Bool × Bool × Bool

/-- A (pure) state of three qubits: an amplitude for each computational basis label. -/
abbrev State := Three → ℂ

/-- The GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz : State :=
  fun s => if s.1 = s.2.1 ∧ s.2.1 = s.2.2 then (1 : ℂ) / Real.sqrt 2 else 0

/-- The `±1` sign attached to a bit: `+1` for `true`, `-1` for `false`. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

/-- Pauli `X` on the first qubit. -/
def X1 (ψ : State) : State := fun s => ψ (!s.1, s.2.1, s.2.2)
/-- Pauli `X` on the second qubit. -/
def X2 (ψ : State) : State := fun s => ψ (s.1, !s.2.1, s.2.2)
/-- Pauli `X` on the third qubit. -/
def X3 (ψ : State) : State := fun s => ψ (s.1, s.2.1, !s.2.2)

/-- Pauli `Y` on the first qubit. -/
def Y1 (ψ : State) : State := fun s => sgn s.1 * Complex.I * ψ (!s.1, s.2.1, s.2.2)
/-- Pauli `Y` on the second qubit. -/
def Y2 (ψ : State) : State := fun s => sgn s.2.1 * Complex.I * ψ (s.1, !s.2.1, s.2.2)
/-- Pauli `Y` on the third qubit. -/
def Y3 (ψ : State) : State := fun s => sgn s.2.2 * Complex.I * ψ (s.1, s.2.1, !s.2.2)

section Eigen

/-- `X ⊗ X ⊗ X` has the GHZ state as a `+1` eigenvector. -/
theorem XXX_ghz : X1 (X2 (X3 ghz)) = ghz := by
  funext s
  obtain ⟨a, b, c⟩ := s
  cases a <;> cases b <;> cases c <;>
    simp [X1, X2, X3, ghz]

/-- `X ⊗ Y ⊗ Y` has the GHZ state as a `-1` eigenvector. -/
theorem XYY_ghz : X1 (Y2 (Y3 ghz)) = -ghz := by
  funext s
  obtain ⟨a, b, c⟩ := s
  cases a <;> cases b <;> cases c <;>
    simp [X1, Y2, Y3, ghz, sgn] <;>
    ring_nf <;>
    simp [Complex.I_sq]

/-- `Y ⊗ X ⊗ Y` has the GHZ state as a `-1` eigenvector. -/
theorem YXY_ghz : Y1 (X2 (Y3 ghz)) = -ghz := by
  funext s
  obtain ⟨a, b, c⟩ := s
  cases a <;> cases b <;> cases c <;>
    simp [Y1, X2, Y3, ghz, sgn] <;>
    ring_nf <;>
    simp [Complex.I_sq]

/-- `Y ⊗ Y ⊗ X` has the GHZ state as a `-1` eigenvector. -/
theorem YYX_ghz : Y1 (Y2 (X3 ghz)) = -ghz := by
  funext s
  obtain ⟨a, b, c⟩ := s
  cases a <;> cases b <;> cases c <;>
    simp [Y1, Y2, X3, ghz, sgn] <;>
    ring_nf <;>
    simp [Complex.I_sq]

/-- The GHZ state is not the zero vector, so the eigenvalue equations above really are
statements about a genuine state (in particular `+1 ≠ -1` matters). -/
theorem ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have h0 := congrFun h (false, false, false)
  simp [ghz] at h0

end Eigen

/-- A deterministic local hidden variable model for the three parties: for a fixed value of
the hidden variable, each party `A`, `B`, `C` has a predetermined outcome `±1` for each of its
two measurement settings (`false = X`, `true = Y`), independent of the other parties' settings. -/
structure LHV where
  A : Bool → ℤ
  B : Bool → ℤ
  C : Bool → ℤ
  hA : ∀ s, A s = 1 ∨ A s = -1
  hB : ∀ s, B s = 1 ∨ B s = -1
  hC : ∀ s, C s = 1 ∨ C s = -1

/--
**GHZ / Mermin nonlocality.**

The first four conjuncts are the quantum mechanical predictions for the GHZ state
`(|000⟩ + |111⟩)/√2`: it is a simultaneous eigenvector of `XYY`, `YXY`, `YYX` with eigenvalue
`-1`, and of `XXX` with eigenvalue `+1`.  Hence measuring these commuting observables yields
outcome products `-1, -1, -1` and `+1` with certainty.

The last conjunct says that no deterministic local hidden variable model can reproduce these
four deterministic predictions: multiplying the three `-1` relations gives
`A(X)B(X)C(X) · (A(Y)B(Y)C(Y))² = -1`, i.e. `A(X)B(X)C(X) = -1`, contradicting the `XXX`
prediction `+1`.
-/
theorem ghz_nonlocal :
    ghz ≠ 0 ∧
    X1 (Y2 (Y3 ghz)) = -ghz ∧
    Y1 (X2 (Y3 ghz)) = -ghz ∧
    Y1 (Y2 (X3 ghz)) = -ghz ∧
    X1 (X2 (X3 ghz)) = ghz ∧
    ∀ m : LHV,
      ¬ (m.A false * m.B true * m.C true = -1 ∧
         m.A true * m.B false * m.C true = -1 ∧
         m.A true * m.B true * m.C false = -1 ∧
         m.A false * m.B false * m.C false = 1) := by
  refine ⟨ghz_ne_zero, XYY_ghz, YXY_ghz, YYX_ghz, XXX_ghz, ?_⟩
  rintro ⟨A, B, C, hA, hB, hC⟩ ⟨h1, h2, h3, h4⟩
  have sA : A true * A true = 1 := by rcases hA true with h | h <;> rw [h] <;> ring
  have sB : B true * B true = 1 := by rcases hB true with h | h <;> rw [h] <;> ring
  have sC : C true * C true = 1 := by rcases hC true with h | h <;> rw [h] <;> ring
  have key : (-1 : ℤ) = 1 :=
    calc (-1 : ℤ)
        = (A false * B true * C true) * (A true * B false * C true) *
            (A true * B true * C false) := by rw [h1, h2, h3]; ring
      _ = (A false * B false * C false) *
            ((A true * A true) * ((B true * B true) * (C true * C true))) := by ring
      _ = 1 := by rw [h4, sA, sB, sC]; ring
  norm_num at key

end QC

#print axioms QC.ghz_nonlocal

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

