import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace QI

/-! ## Setup

Nine qubits, indexed by `Idx = Fin 3 × Fin 3`: the first component is the block
(one of the three "outer" repetition-code slots), the second is the position of the
qubit inside its block.  A computational basis state is a bit string `Idx → Bool`,
and the state space is the corresponding `512`-dimensional complex Hilbert space. -/

/-- Index of a qubit: `(block, position within block)`. -/
abbrev Idx := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev BasisIdx := Idx → Bool

/-- The nine-qubit state space. -/
abbrev QState := EuclideanSpace ℂ BasisIdx

/-- The operator acting as the `2 × 2` matrix `M` on qubit `q` and as the identity
on the remaining eight qubits.  Every single-qubit error on qubit `q` is of this form. -/

lemma inner_qubitOp_bvec (q r : Idx) (M N : Bool → Bool → ℂ) (s t : Bool × Bool × Bool) :
    ⟪qubitOp q M (bvec s), qubitOp r N (bvec t)⟫_ℂ =
      if s = t then gmat q r M N (emb s q) (emb s r) else 0 := by
  rw [inner_apply]
  simp only [bvec, qubitOp_single_apply]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    by_cases hqr : q = r
    · -- same qubit: two basis states contribute
      subst hqr
      rw [Finset.sum_eq_add_of_mem (Function.update (emb s) q false)
          (Function.update (emb s) q true) (Finset.mem_univ _) (Finset.mem_univ _)]
      · have h1 : Function.update (Function.update (emb s) q false) q (emb s q) = emb s := by
          simp [Function.update_idem]
        have h2 : Function.update (Function.update (emb s) q true) q (emb s q) = emb s := by
          simp [Function.update_idem]
        rw [h1, h2]
        simp only [gmat, Function.update_self, Fintype.sum_bool, if_true]
        ring
      · intro h
        have := congrFun h q
        simp at this
      · rintro x - ⟨hx1, hx2⟩
        by_cases hc : Function.update x q (emb s q) = emb s
        · exfalso
          have hxb : x = Function.update (emb s) q (x q) := by
            funext p
            by_cases hp : p = q
            · subst hp; simp
            · have := congrFun hc p
              rw [Function.update_of_ne hp] at this
              rw [Function.update_of_ne hp, this]
          cases hxq : x q
          · exact hx1 (by rw [hxb, hxq])
          · exact hx2 (by rw [hxb, hxq])
        · simp [hc]
    · -- distinct qubits: only one basis state contributes
      rw [Finset.sum_eq_single_of_mem (emb s) (Finset.mem_univ _)]
      · rw [gmat, if_neg hqr]
        simp
      · rintro x - hx
        by_cases hc1 : Function.update x q (emb s q) = emb s
        · by_cases hc2 : Function.update x r (emb s r) = emb s
          · exfalso
            apply hx
            funext p
            by_cases hp : p = q
            · subst hp
              have := congrFun hc2 p
              rwa [Function.update_of_ne hqr] at this
            · have := congrFun hc1 p
              rwa [Function.update_of_ne hp] at this
          · simp [hc2]
        · simp [hc1]
  · -- different block values: no overlap at all
    rw [if_neg hst]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hc1 : Function.update x q (emb s q) = emb s
    · by_cases hc2 : Function.update x r (emb t r) = emb t
      · exfalso
        apply hst
        apply emb_inj_off_two (q := q) (r := r)
        intro p hp1 hp2
        have e1 := congrFun hc1 p
        have e2 := congrFun hc2 p
        rw [Function.update_of_ne hp1] at e1
        rw [Function.update_of_ne hp2] at e2
        rw [← e1, ← e2]
      · simp [hc2]
    · simp [hc1]

/-! ## Sign bookkeeping -/

