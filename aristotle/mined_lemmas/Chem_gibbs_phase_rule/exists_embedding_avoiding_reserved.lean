import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

namespace Chem

/-- Index set of the intensive variables of a heterogeneous system with `C` components
distributed over `P` phases: the two field variables (temperature and pressure), encoded by
`Bool`, together with the mole fraction `x j i` of component `i` in phase `j`.
Hence there are `2 + P * C` variables. -/
abbrev VarIndex (C P : ℕ) : Type := Bool ⊕ (Fin P × Fin C)

/-- Index set of the equilibrium constraints: one normalization condition
`∑ i, x j i = 1` per phase `j` (that is `P` conditions), together with the equalities of
chemical potentials between consecutive phases, `μ i (j) = μ i (j+1)`, one for each component
`i` and each of the `P - 1` consecutive pairs of phases.
Hence there are `P + (P - 1) * C` constraints. -/
abbrev ConIndex (C P : ℕ) : Type := Fin P ⊕ (Fin (P - 1) × Fin C)

/-- The number of intensive variables is `2 + P * C`. -/

lemma exists_embedding_avoiding_reserved (C P : ℕ) (hC : 1 ≤ C) (hPC : P ≤ C + 2) :
    ∃ e : (Fin (P - 1) × Fin C) ↪ VarIndex C P,
      ∀ (c : Fin (P - 1) × Fin C) (j : Fin P), e c ≠ Sum.inr (j, (⟨0, hC⟩ : Fin C)) := by
  classical
  have hcard : Fintype.card (Fin (P - 1) × Fin C)
      ≤ Fintype.card (Bool ⊕ (Fin P × Fin (C - 1))) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
    rcases P with _ | q
    · simp
    · simp only [Nat.succ_sub_one]
      have h1 : q * (c + 1) = q * c + q := by ring
      have h2 : (q + 1) * c = q * c + c := by ring
      omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨f.trans ⟨Sum.elim (fun t => Sum.inl t)
      (fun q => Sum.inr (q.1, ⟨q.2.1 + 1, by have := q.2.isLt; omega⟩)), ?_⟩, ?_⟩
  · rintro (a | a) (b | b) h <;> simp_all [Fin.ext_iff, Prod.ext_iff]
  · rintro c j
    simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    rcases h : f c with a | a <;> simp [Fin.ext_iff]

/-- Non-vacuity of the explicit form of the phase rule: whenever there is at least one component
and `P ≤ C + 2` (the range in which the predicted number of degrees of freedom is nonnegative),
there are linearized chemical potentials `mu` whose equilibrium constraints really are
independent, i.e. for which `constraintMap C P mu` is surjective. -/
