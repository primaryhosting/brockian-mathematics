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

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace QI

namespace Steane

/-! ## The classical `[7,4,3]` Hamming code

`steaneH i j` is the `(i,j)` entry of the parity-check matrix of the Hamming code:
the `i`-th binary digit of the column index `j + 1`.  Explicitly the matrix is

```
1 0 1 0 1 0 1
0 1 1 0 0 1 1
0 0 0 1 1 1 1
```
-/

/-- Parity-check matrix of the classical `[7,4,3]` Hamming code, over `GF(2) = ZMod 2`. -/
def steaneH : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  Matrix.of fun i j => if ((j.val + 1) >>> i.val) % 2 = 1 then 1 else 0

/-- The classical syndrome of a binary vector. -/
def csynd (e : Fin 7 → ZMod 2) : Fin 3 → ZMod 2 := steaneH.mulVec e

/-! ## Pauli errors on 7 qubits

A Pauli error (up to phase) on `n` qubits is described by its symplectic representation
`(x, z) ∈ (GF(2)^n)²`: qubit `j` carries `X^(x j) Z^(z j)`. -/

/-- A Pauli error on the 7 qubits, in symplectic (`X`-part, `Z`-part) representation. -/
abbrev PauliErr : Type := (Fin 7 → ZMod 2) × (Fin 7 → ZMod 2)

/-- The pair of syndromes measured by the Steane code stabilizers: the `X`-type stabilizers
(given by `steaneH`) detect the `Z`-part of the error, and the `Z`-type stabilizers (also
given by `steaneH`, this is a CSS code) detect the `X`-part. -/
def syndrome (E : PauliErr) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (csynd E.2, csynd E.1)

/-- The weight of a Pauli error: the number of qubits on which it acts nontrivially. -/
def wt (E : PauliErr) : ℕ :=
  (Finset.univ.filter (fun j : Fin 7 => E.1 j ≠ 0 ∨ E.2 j ≠ 0)).card

/-- The single-qubit Pauli error acting on qubit `q` by `X^a Z^b`. -/
def single (q : Fin 7) (a b : ZMod 2) : PauliErr := (Pi.single q a, Pi.single q b)

/-! ## CSS structure -/

/-- The Steane code is a CSS code: since `H Hᵀ = 0`, its `X`-type and `Z`-type stabilizer
generators commute. -/
theorem steaneH_mul_transpose : steaneH * steaneH.transpose = 0 := by
  decide

/-- The classical Hamming code (the kernel of `steaneH`) has `2⁴ = 16` codewords,
so it encodes 4 classical bits. -/
theorem hamming_kernel_card :
    (Finset.univ.filter (fun v : Fin 7 → ZMod 2 => steaneH.mulVec v = 0)).card = 16 := by
  decide

/-- The classical Hamming code has minimum distance 3: every nonzero codeword has weight
at least 3. -/
theorem hamming_min_distance :
    ∀ v : Fin 7 → ZMod 2, steaneH.mulVec v = 0 → v ≠ 0 →
      3 ≤ (Finset.univ.filter (fun j : Fin 7 => v j ≠ 0)).card := by
  decide

/-- The dual code (the row space of `steaneH`) is contained in the Hamming code; this is the
CSS condition `C⊥ ⊆ C`. -/
theorem dual_subset_hamming (c : Fin 3 → ZMod 2) :
    steaneH.mulVec (steaneH.vecMul c) = 0 := by
  rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, steaneH_mul_transpose,
    Matrix.zero_mulVec]

/-! ## Weight-one errors -/

/-- A Pauli error has weight at most one exactly when it is a single-qubit error. -/
theorem wt_le_one_iff (E : PauliErr) : wt E ≤ 1 ↔ ∃ q a b, E = single q a b := by
  classical
  constructor
  · intro h
    rw [wt, Finset.card_le_one_iff_subset_singleton] at h
    obtain ⟨q, hq⟩ := h
    refine ⟨q, E.1 q, E.2 q, ?_⟩
    have key : ∀ j : Fin 7, j ≠ q → E.1 j = 0 ∧ E.2 j = 0 := by
      intro j hj
      by_contra hc
      have hmem : j ∈ Finset.univ.filter (fun j : Fin 7 => E.1 j ≠ 0 ∨ E.2 j ≠ 0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h1 : E.1 j = 0
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      exact hj (Finset.mem_singleton.mp (hq hmem))
    have h1 : E.1 = Pi.single q (E.1 q) := by
      funext j
      by_cases hj : j = q
      · subst hj; simp
      · rw [Pi.single_eq_of_ne hj, (key j hj).1]
    have h2 : E.2 = Pi.single q (E.2 q) := by
      funext j
      by_cases hj : j = q
      · subst hj; simp
      · rw [Pi.single_eq_of_ne hj, (key j hj).2]
    exact Prod.ext h1 h2
  · rintro ⟨q, a, b, rfl⟩
    rw [wt, Finset.card_le_one_iff_subset_singleton]
    refine ⟨q, ?_⟩
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, single, ne_eq,
      Pi.single_apply] at hj
    simp only [Finset.mem_singleton]
    by_contra hc
    simp [hc] at hj

/-- **Key combinatorial fact.**  Distinct single-qubit Pauli errors have distinct syndromes:
the syndrome map is injective on single-qubit errors. -/
theorem syndrome_injective_on_single (q₁ q₂ : Fin 7) (a₁ b₁ a₂ b₂ : ZMod 2)
    (h : syndrome (single q₁ a₁ b₁) = syndrome (single q₂ a₂ b₂)) :
    single q₁ a₁ b₁ = single q₂ a₂ b₂ := by
  revert h
  revert q₁ q₂ a₁ b₁ a₂ b₂
  decide

/-- The syndrome map is injective on the set of Pauli errors of weight at most one. -/
theorem syndrome_injective_wt_le_one {E₁ E₂ : PauliErr} (h₁ : wt E₁ ≤ 1) (h₂ : wt E₂ ≤ 1)
    (h : syndrome E₁ = syndrome E₂) : E₁ = E₂ := by
  obtain ⟨q₁, a₁, b₁, rfl⟩ := (wt_le_one_iff E₁).mp h₁
  obtain ⟨q₂, a₂, b₂, rfl⟩ := (wt_le_one_iff E₂).mp h₂
  exact syndrome_injective_on_single q₁ q₂ a₁ b₁ a₂ b₂ h

end Steane

open Steane in
/-- **The 7-qubit Steane (CSS) code corrects any single-qubit error.**

Formally: there is a recovery (decoding) map from measured stabilizer syndromes to Pauli
operators which returns exactly the error that occurred, for *every* Pauli error acting on at
most one of the seven qubits.  Equivalently, the stabilizer syndrome separates all
weight-`≤ 1` Pauli errors, which is the Knill–Laflamme error-correction condition for a
stabilizer code of distance 3. -/
theorem steane_code :
    ∃ recover : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) → PauliErr,
      ∀ E : PauliErr, wt E ≤ 1 → recover (syndrome E) = E := by
  classical
  refine ⟨fun s => if h : ∃ E : PauliErr, wt E ≤ 1 ∧ syndrome E = s then h.choose else (0, 0), ?_⟩
  intro E hE
  have hex : ∃ E' : PauliErr, wt E' ≤ 1 ∧ syndrome E' = syndrome E := ⟨E, hE, rfl⟩
  dsimp only
  rw [dif_pos hex]
  obtain ⟨hw, hs⟩ := hex.choose_spec
  exact syndrome_injective_wt_le_one hw hE hs

open Steane in
/-- Consequence: every nontrivial single-qubit error is *detected*, i.e. produces a nonzero
syndrome. -/
theorem steane_detects_single (E : PauliErr) (hE : wt E ≤ 1) (hne : E ≠ (0, 0)) :
    syndrome E ≠ syndrome (0, 0) :=
  fun h => hne (syndrome_injective_wt_le_one hE (by simp [wt]) h)

end QI

