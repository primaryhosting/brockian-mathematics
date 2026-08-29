import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace QI

/-! ## Setup

The Steane code is the `[[7,1,3]]` CSS code built from the classical `[7,4,3]` Hamming
code `C = ker H`, whose parity–check matrix `H` has as columns the seven nonzero
vectors of `Bit³`.

A Pauli error on `7` qubits is, up to an irrelevant global phase, described by its
symplectic (X-part, Z-part) representation: a pair of bits at every qubit.  The
error syndrome of such an error is the pair of classical Hamming syndromes of its
X-part and of its Z-part (the X-part is detected by the three Z-type stabilizer
generators and the Z-part by the three X-type generators, both given by the rows
of `H`).

"Correcting any single-qubit error" is then the statement that a decoder exists which
recovers the error *exactly* from its syndrome, for every error supported on at most
one qubit.  This is precisely non-degenerate correctability of the single-qubit error
set (the Knill–Laflamme conditions for a stabilizer code reduce to this combinatorial
statement).
-/

/-- Bits, i.e. elements of `GF(2)`. -/
abbrev Bit := ZMod 2

/-- Parity–check matrix of the classical `[7,4,3]` Hamming code: the `j`-th column is
the binary expansion of `j + 1`. -/
def H : Fin 3 → Fin 7 → Bit :=
  ![![1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 1, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1]]

/-- A Pauli error on 7 qubits, in symplectic representation: at each qubit a pair
`(x, z)` of bits, standing for the Pauli operator `X^x Z^z` on that qubit. -/
abbrev PauliError := Fin 7 → Bit × Bit

/-- The error syndrome: the Hamming syndrome of the X-part together with the Hamming
syndrome of the Z-part. -/
def syndrome (E : PauliError) : (Fin 3 → Bit) × (Fin 3 → Bit) :=
  (fun k => ∑ j, H k j * (E j).1, fun k => ∑ j, H k j * (E j).2)

/-- The Pauli error acting as `p` on qubit `i` and trivially elsewhere. -/
def single (i : Fin 7) (p : Bit × Bit) : PauliError := fun j => if j = i then p else (0, 0)

/-- An error is a *single-qubit* error if it is supported on at most one qubit. -/
def SingleQubit (E : PauliError) : Prop := ∃ i : Fin 7, ∀ j, j ≠ i → E j = (0, 0)

/-! ## Classical CSS ingredients -/

/-- Membership in the classical Hamming code `C = ker H`. -/
def InHamming (v : Fin 7 → Bit) : Prop := ∀ k, ∑ j, H k j * v j = 0

instance (v : Fin 7 → Bit) : Decidable (InHamming v) :=
  inferInstanceAs (Decidable (∀ k, ∑ j, H k j * v j = 0))

/-- Hamming weight of a binary word. -/
def wt (v : Fin 7 → Bit) : ℕ := (Finset.univ.filter fun j => v j ≠ 0).card

/-- The Hamming code `C = ker H` has minimum distance `3`. -/
theorem hamming_min_distance :
    ∀ v : Fin 7 → Bit, InHamming v → v ≠ (fun _ => 0) → 3 ≤ wt v := by decide

/-- The distance `3` is attained, so the minimum distance is exactly `3`. -/
theorem hamming_distance_attained :
    ∃ v : Fin 7 → Bit, InHamming v ∧ v ≠ (fun _ => 0) ∧ wt v = 3 := by decide

/-- Self-orthogonality of `H`: `H Hᵀ = 0`.  Equivalently `C^⊥ ⊆ C`, which is the CSS
condition making the X-type and Z-type stabilizer generators commute. -/
theorem css_dual_containment : ∀ k l : Fin 3, ∑ j, H k j * H l j = 0 := by decide

/-- Every row of `H` is itself a codeword; together with `css_dual_containment` this is
the statement `C^⊥ ⊆ C`. -/
theorem rows_mem_hamming (k : Fin 3) : InHamming (H k) := fun l => by
  simpa [mul_comm] using css_dual_containment l k

/-! ## Distinctness of single-qubit syndromes -/

/-- Distinct single-qubit Pauli errors have distinct syndromes: the Steane code is a
non-degenerate code correcting one error. -/
theorem syndrome_single_injective :
    ∀ (i j : Fin 7) (p q : Bit × Bit),
      syndrome (single i p) = syndrome (single j q) → single i p = single j q := by decide

/-- Any single-qubit error is of the form `single i p`. -/
theorem SingleQubit.exists_single {E : PauliError} (h : SingleQubit E) :
    ∃ (i : Fin 7) (p : Bit × Bit), E = single i p := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, E i, funext fun j => ?_⟩
  by_cases hj : j = i
  · simp [single, hj]
  · simp [single, hj, hi j hj]

/-- The syndrome map is injective on single-qubit errors. -/
theorem syndrome_injOn {E F : PauliError} (hE : SingleQubit E) (hF : SingleQubit F)
    (h : syndrome E = syndrome F) : E = F := by
  obtain ⟨i, p, rfl⟩ := hE.exists_single
  obtain ⟨j, q, rfl⟩ := hF.exists_single
  exact syndrome_single_injective i j p q h

/-! ## Main theorem -/

/-- The decoder: given a syndrome, return the (unique, by `syndrome_injOn`) single-qubit
error producing it, if there is one. -/
noncomputable def decoder (s : (Fin 3 → Bit) × (Fin 3 → Bit)) : PauliError :=
  @dite _ (∃ E : PauliError, SingleQubit E ∧ syndrome E = s) (Classical.propDecidable _)
    (fun h => h.choose) (fun _ => fun _ => (0, 0))

/-- **The 7-qubit Steane code corrects any single-qubit error.**

There is a decoder `dec`, taking an error syndrome to a Pauli error, which recovers
*exactly* the error that occurred, for every Pauli error supported on at most one of
the seven qubits.  Applying `dec (syndrome E)` as a recovery operation therefore undoes
`E` on the nose. -/
theorem steane_code :
    ∃ dec : (Fin 3 → Bit) × (Fin 3 → Bit) → PauliError,
      ∀ E : PauliError, SingleQubit E → dec (syndrome E) = E := by
  refine ⟨decoder, fun E hE => ?_⟩
  have hex : ∃ F : PauliError, SingleQubit F ∧ syndrome F = syndrome E := ⟨E, hE, rfl⟩
  rw [decoder, dif_pos hex]
  obtain ⟨hF, hFs⟩ := hex.choose_spec
  exact syndrome_injOn hF hE hFs

end QI

