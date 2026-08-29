import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

set_option grind.warning false

namespace Frontier

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

theorem kneser_double_chromaticNumber (k : ℕ) (hk : 1 ≤ k) :
    (kneserGraph (2 * k) k).chromaticNumber = 2 := by
  classical
  have hcol : (kneserGraph (2 * k) k).Colorable 2 := by
    have h := kneser_colorable (2 * k) k hk le_rfl
    have he : 2 * k - 2 * k + 2 = 2 := by omega
    rwa [he] at h
  refine le_antisymm hcol.chromaticNumber_le ?_
  have hlow : ((2 : ℕ) : ℕ∞) ≤ (kneserGraph (2 * k) k).chromaticNumber := by
    have hlt : (Finset.univ.filter (fun y : Fin (2 * k) => (y : ℕ) < k)).card = k :=
      card_filter_val_lt _ _ (by omega)
    have hge : (Finset.univ.filter (fun y : Fin (2 * k) => k ≤ (y : ℕ))).card = k := by
      rw [card_filter_le_val]
      omega
    set S : KneserVertex (2 * k) k :=
      ⟨Finset.univ.filter (fun y : Fin (2 * k) => (y : ℕ) < k), hlt⟩ with hS
    set T : KneserVertex (2 * k) k :=
      ⟨Finset.univ.filter (fun y : Fin (2 * k) => k ≤ (y : ℕ)), hge⟩ with hT
    have hdisj : Disjoint (S : Finset (Fin (2 * k))) (T : Finset (Fin (2 * k))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      omega
    have hSne : S ≠ T := by
      intro h
      have hnonempty : (S : Finset (Fin (2 * k))).Nonempty := by
        rw [← Finset.card_pos, hlt]
        omega
      obtain ⟨x, hx⟩ := hnonempty
      exact (Finset.disjoint_left.mp hdisj hx) (h ▸ hx)
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin 2) (by simp)
      (fun i => if i = 0 then S else T) ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hSne, hdisj, hdisj.symm, Ne.symm hSne]
  exact_mod_cast hlow

/-! ## The main statement -/

/-- **Lovász–Kneser theorem (base cases).**

The chromatic number of the Kneser graph `KG_{n,k}` equals `n - 2k + 2`.  This is established
here in the base cases `k = 1` (where `KG_{n,1}` is the complete graph `K_n`) and `n ≤ 2k + 1`
(where `KG_{2k,k}` is a perfect matching and `KG_{2k+1,k}` is the odd Kneser graph, of
chromatic number `3`).  The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is proved in full generality
in `Frontier.kneser_colorable`.  The general lower bound is Lovász's theorem, whose known
proofs go through the Borsuk–Ulam theorem (or Tucker's lemma), which is not currently
available in Mathlib. -/
