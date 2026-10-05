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
open scoped Matrix
open scoped ComplexOrder

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

-- Note: the header block above is placed directly after `import Mathlib` because Lean requires
-- every `import` to precede all other commands, including module documentation comments.

namespace QI

/-! ## Auxiliary linear algebra: rank factorizations -/

/-- `LinearMap.toMatrix'` is inverse to `Matrix.mulVecLin`. -/

theorem card_le_of_two_correctable {n q K : ℕ} (ψ : Fin K → (Fin n → Fin q) → ℂ) (hψ : ψ ≠ 0)
    (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB)
    (hcA : ErasureCorrectable ψ SA) (hcB : ErasureCorrectable ψ SB) :
    K ≤ q ^ (n - SA.card - SB.card) := by
  classical
  obtain ⟨gA, hgA⟩ := hcA
  obtain ⟨gB, hgB⟩ := hcB
  set Ψ : Fin K → ({i : Fin n // i ∈ SA} → Fin q) → ({i : Fin n // i ∈ SB} → Fin q) →
      ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) → ℂ :=
    fun i a b c => ψ i (combine SA SB a b c) with hΨdef
  have hΨ : Ψ ≠ 0 := by
    intro h
    apply hψ
    funext i x
    have := congrFun (congrFun (congrFun (congrFun h i) (fun s => x s.val))
      (fun s => x s.val)) (fun s => x s.val)
    simpa [hΨdef, combine_restrict] using this
  have h1 : ∀ (i j : Fin K) (a a' : {i : Fin n // i ∈ SA} → Fin q),
      (∑ b, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a' b c))
        = (if i = j then 1 else 0) * (Matrix.of gA) a a' := by
    intro i j a a'
    calc (∑ b, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a' b c))
        = ∑ bc : ({i : Fin n // i ∈ SB} → Fin q) × ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q),
            Ψ i a bc.1 bc.2 * (starRingEnd ℂ) (Ψ j a' bc.1 bc.2) :=
          (Fintype.sum_prod_type fun bc => Ψ i a bc.1 bc.2 * (starRingEnd ℂ) (Ψ j a' bc.1 bc.2)).symm
      _ = ∑ y, ψ i (glue SA a y) * (starRingEnd ℂ) (ψ j (glue SA a' y)) :=
          Fintype.sum_bijective _ (mergeA_bijective SA SB hdisj) _ _
            (fun bc => by simp [hΨdef, combine_eq_glueA])
      _ = _ := hgA i j a a'
  have h2 : ∀ (i j : Fin K) (b b' : {i : Fin n // i ∈ SB} → Fin q),
      (∑ a, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a b' c))
        = (if i = j then 1 else 0) * (Matrix.of gB) b b' := by
    intro i j b b'
    calc (∑ a, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a b' c))
        = ∑ ac : ({i : Fin n // i ∈ SA} → Fin q) × ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q),
            Ψ i ac.1 b ac.2 * (starRingEnd ℂ) (Ψ j ac.1 b' ac.2) :=
          (Fintype.sum_prod_type fun ac => Ψ i ac.1 b ac.2 * (starRingEnd ℂ) (Ψ j ac.1 b' ac.2)).symm
      _ = ∑ y, ψ i (glue SB b y) * (starRingEnd ℂ) (ψ j (glue SB b' y)) :=
          Fintype.sum_bijective _ (mergeB_bijective SA SB hdisj) _ _
            (fun ac => by simp [hΨdef, combine_eq_glueB SA SB hdisj])
      _ = _ := hgB i j b b'
  have hmain := card_le_card_of_correctable Ψ hΨ (Matrix.of gA) (Matrix.of gB) h1 h2
  have hcardC : Fintype.card ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q)
      = q ^ (n - SA.card - SB.card) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Finset.card_compl,
      Finset.card_union_of_disjoint hdisj]
    simp [Nat.sub_sub]
  rw [Fintype.card_fin, hcardC] at hmain
  exact hmain

/-- **Quantum Singleton bound.**

Let `ψ` be an `[[n, k, d]]_q` quantum error correcting code: a code of `q^k` orthonormal
codewords in the space of `n` qudits of local dimension `q` (`horth`) whose distance is at
least `d`, i.e. the erasure of any set of at most `d - 1` qudits is correctable in the sense of
the Knill–Laflamme conditions (`hdist`).

Then `n - k ≥ 2 (d - 1)`, stated here in the subtraction-free form `k + 2 * (d - 1) ≤ n`.

The hypothesis `1 ≤ k` (a nontrivial logical space) is necessary: for `k = 0` a single product
state on one qudit satisfies the Knill–Laflamme conditions for every one-qudit erasure, i.e. it
is a "`[[1, 0, 2]]` code", while `2 * (2 - 1) ≤ 1` fails.

The proof is the rank (Schmidt-rank) version of the entropic argument: writing `R` for the
logical index and splitting the qudits into two correctable regions `A`, `B` of size `d - 1`
and the rest `C`, the Knill–Laflamme conditions give
`rank ρ_{BC} = rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{AC} = |R| · rank ρ_B`, while
`rank ρ_{BC} ≤ rank ρ_B · rank ρ_C` and `rank ρ_{AC} ≤ rank ρ_A · rank ρ_C`; multiplying and
cancelling yields `|R| ≤ rank ρ_C ≤ q^(n - 2(d-1))`. -/
