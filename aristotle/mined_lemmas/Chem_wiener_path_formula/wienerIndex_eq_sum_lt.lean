import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Finset

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances `d(u,v)` over all
unordered pairs `{u, v}` of vertices (the diagonal pairs contribute `0`). -/

theorem wienerIndex_eq_sum_lt {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    wienerIndex G = ∑ p ∈ Finset.univ.offDiag with p.1 < p.2, G.dist p.1 p.2 := by
  set f : Sym2 V → ℕ := Sym2.lift ⟨G.dist, fun _ _ => G.dist_comm⟩ with hf
  have hdiag : ∀ e : Sym2 V, e.IsDiag → f e = 0 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.mk_isDiag_iff] at he
      subst he
      simp [hf]
  have h1 : wienerIndex G = ∑ e ∈ Finset.univ.sym2 with ¬ e.IsDiag, f e := by
    rw [wienerIndex, ← hf, ← Finset.sym2_univ]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ.sym2 (fun e => e.IsDiag) f]
    rw [Finset.sum_eq_zero (fun e he => hdiag e (Finset.mem_filter.1 he).2), zero_add]
  rw [h1, Finset.sum_sym2_filter_not_isDiag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hf, show Sym2.mk x = s(x.1, x.2) from rfl, Sym2.lift_mk]

/-! ### Distances in the path graph -/

/-- In the path graph `P n` there is a walk of length `|i - j|` between any two vertices. -/
