import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Matrix

/-- The Pauli `X` (bit flip) matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` (phase flip) matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The encoding operator that Alice applies to **her single qubit** in order to send the
two classical bits `(a, b)`: it is `X^b * Z^a`, one of the four Pauli operators. -/
def pauli (a b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if b then pauliX else 1) * (if a then pauliZ else 1)

/-- The Bell state `(|00⟩ + |11⟩)/√2` on two qubits, as a vector indexed by
`Fin 2 × Fin 2` (Alice's qubit first, Bob's qubit second). -/
noncomputable def bell : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- Superdense coding: Alice encodes the two classical bits `(a, b)` by applying the Pauli
operator `pauli a b` to her own qubit only (i.e. the operator `pauli a b ⊗ I` on the pair)
and sending that single qubit to Bob. -/
noncomputable def encode (m : Bool × Bool) : Fin 2 × Fin 2 → ℂ :=
  (Matrix.kroneckerMap (· * ·) (pauli m.1 m.2) (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec bell

/-- Each encoding operator is unitary, so Alice's local operation is a legitimate
quantum operation. -/
theorem pauli_unitary (a b : Bool) : (pauli a b)ᴴ * pauli a b = 1 := by
  cases a <;> cases b <;>
    simp [pauli, pauliX, pauliZ, Matrix.conjTranspose, Matrix.mul_fin_two,
      Matrix.one_fin_two, Matrix.ext_iff.symm, Fin.forall_fin_two] <;>
    norm_num [Matrix.one_fin_two, Matrix.ext_iff.symm, Fin.forall_fin_two]

/-- Explicit description of the encoded state: its `(i, j)` amplitude is the `(i, j)` entry of
the Pauli operator divided by `√2`. -/
theorem encode_apply (m : Bool × Bool) (i j : Fin 2) :
    encode m (i, j) = pauli m.1 m.2 i j * ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp only [encode, Matrix.mulVec, Matrix.kroneckerMap_apply, dotProduct, bell,
    Fintype.sum_prod_type]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, Matrix.one_apply] <;> ring

private lemma sqrt2_inv_ne_zero : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  simpa using h

/-- **Superdense coding transmits two classical bits.**
The map sending a two-bit message to the state obtained by applying the corresponding Pauli
operator to Alice's half of a shared Bell pair is injective on the four messages; hence the
single transmitted qubit (together with the prior entanglement) carries two classical bits. -/
theorem superdense_two_bits : Function.Injective encode := by
  have key : ∀ (m : Bool × Bool) (i j : Fin 2),
      encode m (i, j) = pauli m.1 m.2 i j * ((Real.sqrt 2)⁻¹ : ℝ) := encode_apply
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h00 := congrFun h (0, 0)
  have h01 := congrFun h (0, 1)
  have h11 := congrFun h (1, 1)
  rw [key, key] at h00 h01 h11
  have hne := sqrt2_inv_ne_zero
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [pauli, pauliX, pauliZ, Matrix.mul_fin_two, Matrix.one_fin_two]

/-- The four encoded states form an orthonormal family (they are the four Bell states),
so Bob can perfectly distinguish the four messages by a measurement. -/
theorem encode_orthonormal (m m' : Bool × Bool) :
    ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (encode m p) * encode m' p =
      if m = m' then 1 else 0 := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h : Real.sqrt 2 ≠ 0 := by positivity
    exact_mod_cast h
  obtain ⟨a, b⟩ := m
  obtain ⟨c, d⟩ := m'
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, encode_apply]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [pauli, pauliX, pauliZ, Matrix.mul_fin_two, Matrix.one_fin_two, Complex.ext_iff] <;>
    field_simp <;> ring_nf <;> nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0),
      Real.sqrt_nonneg 2]

end QC

