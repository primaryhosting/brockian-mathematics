/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma not_blocky_of_support {d : Bits} {k l : Idx} (hd : d ≠ bzero)
    (h : ∀ q, d q = true → q = k ∨ q = l) : ¬ Blocky d := by
  intro hb
  obtain ⟨q0, hq0⟩ : ∃ q, d q = true := by
    by_contra hcon
    push_neg at hcon
    exact hd (funext fun q => Bool.eq_false_iff.mpr (hcon q))
  obtain ⟨m, p0⟩ := q0
  have hbase : d (m, 0) = true := by rw [← hb (m, p0)]; exact hq0
  have h1 : d (m, 1) = true := by rw [hb (m, 1)]; exact hbase
  have h2 : d (m, 2) = true := by rw [hb (m, 2)]; exact hbase
  have hne : ∀ (p p' : Fin 3), ((m, p) : Idx) = (m, p') → p = p' :=
    fun p p' hpp => congrArg Prod.snd hpp
  rcases h _ hbase with e0 | e0 <;> rcases h _ h1 with e1 | e1 <;> rcases h _ h2 with e2 | e2 <;>
    first
      | exact absurd (hne 0 1 (e0.trans e1.symm)) (by decide)
      | exact absurd (hne 0 2 (e0.trans e2.symm)) (by decide)
      | exact absurd (hne 1 2 (e1.trans e2.symm)) (by decide)

/-! ## The two cases of the core sum -/

