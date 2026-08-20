/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires every
-- `import` to precede any module docstring; the text is otherwise verbatim.)


/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-! ## The binary field and the Hamming parity-check matrix -/

/-- The two-element field `GF(2)`. -/
abbrev F2 := ZMod 2

/-- Column `i` of the parity-check matrix of the `[7,4,3]` Hamming code: the binary
expansion of `i + 1`.  The seven columns are exactly the seven nonzero vectors of
`GF(2)³`, which is what makes the code single-error correcting. -/
def hcol (i : Fin 7) (r : Fin 3) : F2 := if Nat.testBit (i.val + 1) r.val then 1 else 0

/-- The columns of the parity-check matrix are pairwise distinct. -/
theorem hcol_injective : Function.Injective hcol := by decide

/-- No column of the parity-check matrix is zero. -/
theorem hcol_ne_zero (i : Fin 7) : hcol i ≠ 0 := by revert i; decide

/-! ## Pauli errors in the symplectic (binary) representation

A Pauli operator on 7 qubits is written, up to phase, as `X^x Z^z` with
`x, z : Fin 7 → GF(2)`.  Composition is addition of the vectors and commutation is
governed by the symplectic form below; this is the standard binary representation of
the Pauli group used in stabilizer theory. -/

/-- A Pauli operator on the seven qubits, up to phase, in binary symplectic form. -/
structure Pauli where
  /-- The `X`-part of the Pauli operator. -/
  x : Fin 7 → F2
  /-- The `Z`-part of the Pauli operator. -/
  z : Fin 7 → F2

/-- Decidable equality of Paulis, defined component-wise so that it reduces well in the
kernel (the auto-derived instance gets stuck on `Eq.rec`). -/
instance : DecidableEq Pauli := fun P Q =>
  decidable_of_iff (P.x = Q.x ∧ P.z = Q.z) (by cases P; cases Q; simp)

instance : Fintype Pauli :=
  Fintype.ofEquiv ((Fin 7 → F2) × (Fin 7 → F2))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun P => (P.x, P.z)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The symplectic form on Pauli operators: `sympl P Q = 0` exactly when `P` and `Q`
commute, and `sympl P Q = 1` exactly when they anticommute. -/
def sympl (P Q : Pauli) : F2 := ∑ i, (P.x i * Q.z i + P.z i * Q.x i)

/-- The single-qubit Pauli supported at site `i` with `X`-exponent `a`. -/
def ind (i : Fin 7) (a : F2) : Fin 7 → F2 := fun k => if k = i then a else 0

/-- An error is a *single-qubit error* when its support is contained in one qubit. -/
def Pauli.SingleQubit (E : Pauli) : Prop := ∃ i : Fin 7, ∀ k : Fin 7, k ≠ i → E.x k = 0 ∧ E.z k = 0

/-- A single-qubit error is precisely one of the form `X^a Z^b` acting at a single site. -/
theorem singleQubit_iff (E : Pauli) :
    E.SingleQubit ↔ ∃ i : Fin 7, E = ⟨ind i (E.x i), ind i (E.z i)⟩ := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    obtain ⟨x, z⟩ := E
    have hx : x = ind i (x i) := by
      funext k
      by_cases h : k = i
      · subst h; simp [ind]
      · simpa [ind, h] using (hi k h).1
    have hz : z = ind i (z i) := by
      funext k
      by_cases h : k = i
      · subst h; simp [ind]
      · simpa [ind, h] using (hi k h).2
    exact Pauli.mk.injEq .. ▸ ⟨hx, hz⟩
  · rintro ⟨i, hE⟩
    refine ⟨i, fun k hk => ?_⟩
    constructor <;> rw [hE] <;> simp [ind, hk]

/-! ## The Steane code stabilizer -/

/-- The three `Z`-type stabilizer generators of the Steane code, given by the rows of the
Hamming parity-check matrix. -/
def stabZ (r : Fin 3) : Pauli := ⟨0, fun i => hcol i r⟩

/-- The three `X`-type stabilizer generators of the Steane code, given by the rows of the
Hamming parity-check matrix. -/
def stabX (r : Fin 3) : Pauli := ⟨fun i => hcol i r, 0⟩

/-- The six generators pairwise commute, so they do generate an abelian stabilizer group:
this is the CSS condition `H Hᵀ = 0` for the (self-orthogonal) Hamming code. -/
theorem stab_commute :
    (∀ r s : Fin 3, sympl (stabX r) (stabZ s) = 0) ∧
    (∀ r s : Fin 3, sympl (stabX r) (stabX s) = 0) ∧
    (∀ r s : Fin 3, sympl (stabZ r) (stabZ s) = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Syndromes and decoding -/

/-- The parity check `H v` of a binary vector. -/
def synd (v : Fin 7 → F2) : Fin 3 → F2 := fun r => ∑ i, hcol i r * v i

/-- The error syndrome of a Pauli error: the list of commutation relations with the six
stabilizer generators, i.e. the two Hamming syndromes of the `X`- and `Z`-parts. -/
def syndrome (E : Pauli) : (Fin 3 → F2) × (Fin 3 → F2) := (synd E.x, synd E.z)

/-- The syndrome really is the measured commutation data: the `Z`-type generators detect
the `X`-part of the error. -/
theorem syndrome_fst (E : Pauli) (r : Fin 3) : sympl (stabZ r) E = (syndrome E).1 r := by
  simp [sympl, stabZ, syndrome, synd]

/-- The `X`-type generators detect the `Z`-part of the error. -/
theorem syndrome_snd (E : Pauli) (r : Fin 3) : sympl (stabX r) E = (syndrome E).2 r := by
  simp [sympl, stabX, syndrome, synd]

/-- The Hamming decoder: a syndrome `s` points at the unique column of the parity-check
matrix equal to it (and at no qubit at all when `s = 0`). -/
def locate (s : Fin 3 → F2) : Fin 7 → F2 := fun i => if hcol i = s then 1 else 0

/-- The Steane decoder: run the Hamming decoder on each of the two syndromes. -/
def decode (s : (Fin 3 → F2) × (Fin 3 → F2)) : Pauli := ⟨locate s.1, locate s.2⟩

/-- Correctness of the decoder on the single-site errors `X^a Z^b`. -/
theorem decode_ind (i : Fin 7) (a b : F2) :
    decode (syndrome ⟨ind i a, ind i b⟩) = ⟨ind i a, ind i b⟩ := by
  revert i a b; decide

/-- **The decoder recovers every single-qubit error.**  For any Pauli error `E` acting on
at most one of the seven qubits, applying the Steane decoder to the measured syndrome
returns `E` itself, so applying `decode (syndrome E)` undoes the error exactly. -/
theorem steane_decode_correct (E : Pauli) (hE : E.SingleQubit) : decode (syndrome E) = E := by
  obtain ⟨i, hi⟩ := (singleQubit_iff E).1 hE
  rw [hi]
  exact decode_ind i (E.x i) (E.z i)

/-- **The 7-qubit Steane code corrects any single-qubit error.**

Two single-qubit Pauli errors that produce the same syndrome (the same commutation
pattern with the six CSS stabilizer generators of the code) are equal; equivalently, the
explicit decoder `decode` recovers the error exactly from its syndrome
(`steane_decode_correct`).  This is the Knill–Laflamme correctability condition for the
stabilizer code: distinct correctable errors are distinguished by the measured syndrome,
so a recovery operation exists. -/
theorem steane_code :
    (∀ E : Pauli, E.SingleQubit → decode (syndrome E) = E) ∧
    (∀ E F : Pauli, E.SingleQubit → F.SingleQubit → syndrome E = syndrome F → E = F) := by
  refine ⟨steane_decode_correct, fun E F hE hF h => ?_⟩
  rw [← steane_decode_correct E hE, ← steane_decode_correct F hF, h]

end QI

