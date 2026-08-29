/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not allow a `/-! ... -/` module docstring to precede `import`, so the
-- required header comment is reproduced verbatim immediately after the import below.)

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
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

set_option grind.warning false

/-!
## Overview

We prove the **quantum Singleton bound** (Knill–Laflamme–Rains): an `[[n, k, d]]_q`
quantum error-correcting code satisfies `k + 2 * (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The proof given here is a purely linear-algebraic ("Rényi-0"/rank) version of the usual
entropic no-cloning argument.  Writing the code space as a tensor `T` with a reference
index `R` (of size `q ^ k`) and three groups of sites `A`, `B`, `C`, the Knill–Laflamme
conditions for the two disjoint site sets `A` and `B` say that the Gram matrices of the
code vectors, partially traced onto `A` (resp. `B`), are proportional to the identity in
the reference index.  Passing to ranks:

* `rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{RB} = |R| · rank ρ_B`  (Kronecker structure);
* `rank ρ_{BC} ≤ rank ρ_B · rank ρ_C`  (rank submultiplicativity across a tensor cut);
* `rank ρ_{RA} = rank ρ_{BC}` and `rank ρ_{RB} = rank ρ_{AC}` (purity).

Multiplying the two resulting inequalities `|R| · a ≤ b · c` and `|R| · b ≤ a · c` and
cancelling `a·b > 0` gives `|R| ≤ c ≤ q ^ |C|`, which is the bound.

No Mathlib lemma proves this statement (Mathlib contains no quantum coding theory), so the
required linear algebra — in particular a rank factorization of a matrix with one-sided
inverses, the rank of `1 ⊗ₖ S`, and submultiplicativity of the rank across a tensor cut —
is developed here from scratch.
-/

open Matrix Module Kronecker
open scoped ComplexOrder

namespace QI

/-! ### General linear algebra: rank tools -/

/-- **Rank factorization.**  Any matrix `N` factors as `N = F * G` where `F` has `rank N`
columns and a left inverse, and `G` has `rank N` rows and a right inverse. -/

theorem dim_le_of_disjoint {n k d q : ℕ} (hq : 0 < q) (Q : Code n k d q)
    (A B : Finset (Fin n)) (hdisj : Disjoint A B)
    (hAcard : A.card ≤ d - 1) (hBcard : B.card ≤ d - 1) :
    q ^ k ≤ q ^ (n - A.card - B.card) := by
  classical
  set Cs := (A ∪ B)ᶜ with hCsdef
  have hmem : ∀ i : Fin n, (i ∈ A ∧ i ∉ B ∧ i ∉ Cs) ∨ (i ∉ A ∧ i ∈ B ∧ i ∉ Cs)
      ∨ (i ∉ A ∧ i ∉ B ∧ i ∈ Cs) := by
    intro i
    by_cases hia : i ∈ A
    · exact Or.inl ⟨hia, Finset.disjoint_left.mp hdisj hia, by simp [hCsdef, hia]⟩
    · by_cases hib : i ∈ B
      · exact Or.inr (Or.inl ⟨hia, hib, by simp [hCsdef, hib]⟩)
      · exact Or.inr (Or.inr ⟨hia, hib, by simp [hCsdef, hia, hib]⟩)
  have hmem' : ∀ i : Fin n, (i ∈ B ∧ i ∉ A ∧ i ∉ Cs) ∨ (i ∉ B ∧ i ∈ A ∧ i ∉ Cs)
      ∨ (i ∉ B ∧ i ∉ A ∧ i ∈ Cs) := by
    intro i
    rcases hmem i with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨h2, h1, h3⟩)
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
  have hABcard : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  have hle : A.card + B.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ (A ∪ B))
    simp only [Finset.card_univ, Fintype.card_fin, hABcard] at h
    exact h
  have hCscard : Cs.card = n - A.card - B.card := by
    rw [hCsdef, Finset.card_compl, hABcard]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hcard : A.card + B.card + Cs.card = n := by omega
  have hcard' : B.card + A.card + Cs.card = n := by omega
  set e := splitEquiv (q := q) A B Cs hmem hcard with he
  -- the Knill-Laflamme conditions in Gram form, for `A` and for `B`
  obtain ⟨SA, hSA⟩ : ∃ SA : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ,
      ∀ (i j : Fin (q ^ k)) (a a' : {i // i ∈ A} → Fin q),
        ∑ b, ∑ c, Q.state i (e.symm (a, b, c))
            * (starRingEnd ℂ) (Q.state j (e.symm (a', b, c)))
          = if i = j then SA a a' else 0 := by
    have hch : ∀ a a' : {i // i ∈ A} → Fin q, ∃ cc : ℂ, ∀ i j,
        ∑ x, ∑ y, (starRingEnd ℂ) (Q.state i x) * embed A (Matrix.single a a' 1) x y
          * Q.state j y = if i = j then cc else 0 :=
      fun a a' => Q.knill_laflamme A hAcard (Matrix.single a a' 1)
    choose cc hcc using hch
    refine ⟨Matrix.of fun a a' => (starRingEnd ℂ) (cc a a'), ?_⟩
    intro i j a a'
    have h := hcc a a' i j
    rw [kl_sum A B Cs hmem hcard Q a a' i j] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [map_sum, map_mul, Complex.conj_conj, apply_ite (starRingEnd ℂ), map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
  obtain ⟨SB, hSB⟩ : ∃ SB : Matrix ({i // i ∈ B} → Fin q) ({i // i ∈ B} → Fin q) ℂ,
      ∀ (i j : Fin (q ^ k)) (b b' : {i // i ∈ B} → Fin q),
        ∑ a, ∑ c, Q.state i (e.symm (a, b, c))
            * (starRingEnd ℂ) (Q.state j (e.symm (a, b', c)))
          = if i = j then SB b b' else 0 := by
    have hch : ∀ b b' : {i // i ∈ B} → Fin q, ∃ cc : ℂ, ∀ i j,
        ∑ x, ∑ y, (starRingEnd ℂ) (Q.state i x) * embed B (Matrix.single b b' 1) x y
          * Q.state j y = if i = j then cc else 0 :=
      fun b b' => Q.knill_laflamme B hBcard (Matrix.single b b' 1)
    choose cc hcc using hch
    refine ⟨Matrix.of fun b b' => (starRingEnd ℂ) (cc b b'), ?_⟩
    intro i j b b'
    have h := hcc b b' i j
    rw [kl_sum B A Cs hmem' hcard' Q b b' i j] at h
    simp only [splitEquiv_swap A B Cs hmem hcard hmem' hcard'] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [map_sum, map_mul, Complex.conj_conj, apply_ite (starRingEnd ℂ), map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
  -- a nonzero code vector
  have hpos : 0 < q ^ k := pow_pos hq k
  have hne : (fun (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
      (c : {i // i ∈ Cs} → Fin q) => Q.state ⟨0, hpos⟩ (e.symm (a, b, c))) ≠ 0 := by
    intro h
    have hzero : ∀ x, Q.state ⟨0, hpos⟩ x = 0 := by
      intro x
      have := congrFun (congrFun (congrFun h (e x).1) (e x).2.1) (e x).2.2
      simpa using this
    have h1 := Q.orthonormal ⟨0, hpos⟩ ⟨0, hpos⟩
    rw [if_pos rfl] at h1
    simp only [hzero, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  -- apply the abstract bound
  have hmain := card_le_card_of_decoupled
    (fun (i : Fin (q ^ k)) a b c => Q.state i (e.symm (a, b, c))) SA SB hSA hSB ⟨0, hpos⟩ hne
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_coe, hCscard] at hmain
  exact hmain

/-- **The quantum Singleton bound.**

For an `[[n, k, d]]_q` quantum error-correcting code with `q ≥ 2` local dimensions and at
least one encoded qudit (`k ≥ 1`), one has `k + 2 (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The hypothesis `1 ≤ k` cannot be dropped with this (standard, Knill–Laflamme) definition of
the distance: for a one-dimensional code space the Knill–Laflamme conditions hold vacuously
for every error, so e.g. a single qubit would be an `[[1, 0, d]]` code for every `d`.  (For
`k = 0` the usual convention additionally demands that all reduced density matrices on
`d - 1` sites be maximally mixed.) -/
