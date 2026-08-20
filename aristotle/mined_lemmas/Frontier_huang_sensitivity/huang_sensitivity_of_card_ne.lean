import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

theorem huang_sensitivity_of_card_ne (hn : 1 ≤ n) (f : Q n → Bool)
    (hf : (univ.filter (fun x => f x ≠ par x)).card ≠ 2 ^ (n - 1)) :
    Real.sqrt n ≤ sensitivity f := by
  classical
  set S : Finset (Q n) := univ.filter (fun x => f x ≠ par x) with hSdef
  have hcardQ : Fintype.card (Q n) = 2 ^ n := by simp
  have hcompl : S.card + Sᶜ.card = 2 ^ n := by
    rw [Finset.card_compl, hcardQ]
    have : S.card ≤ 2 ^ n := by
      simpa [hcardQ] using (Finset.card_le_univ S)
    omega
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  -- choose the fibre of `f ⊕ par` which is larger than half of the cube
  obtain ⟨T, hTcard, hTsame⟩ :
      ∃ T : Finset (Q n), 2 ^ (n - 1) < T.card ∧
        ∀ x ∈ T, ∀ i : Fin n, flipAt x i ∈ T → f (flipAt x i) ≠ f x := by
    rcases lt_or_gt_of_ne hf with hlt | hgt
    · refine ⟨Sᶜ, by omega, ?_⟩
      intro x hx i hy
      have hx' : f x = par x := by
        by_contra hc
        exact (Finset.mem_compl.1 hx) (by simp [hSdef, hc])
      have hy' : f (flipAt x i) = par (flipAt x i) := by
        by_contra hc
        exact (Finset.mem_compl.1 hy) (by simp [hSdef, hc])
      have hpar := par_flipAt x i
      rw [hx', hy']
      exact hpar
    · refine ⟨S, hgt, ?_⟩
      intro x hx i hy
      have hx' : f x ≠ par x := by simpa [hSdef] using hx
      have hy' : f (flipAt x i) ≠ par (flipAt x i) := by simpa [hSdef] using hy
      have hpar := par_flipAt x i
      revert hx' hy' hpar
      cases f x <;> cases f (flipAt x i) <;> cases par x <;> cases par (flipAt x i) <;> simp
  obtain ⟨x, hxT, hx⟩ := huang_cube hn T hTcard
  refine hx.trans ?_
  have hsub : univ.filter (fun i : Fin n => flipAt x i ∈ T)
      ⊆ univ.filter (fun i : Fin n => f (flipAt x i) ≠ f x) := by
    intro i hi
    have : flipAt x i ∈ T := by simpa using hi
    simp [hTsame x hxT i this]
  have h1 : (univ.filter (fun i : Fin n => flipAt x i ∈ T)).card ≤ sens f x :=
    Finset.card_le_card hsub
  have h2 : sens f x ≤ sensitivity f := Finset.le_sup (Finset.mem_univ x)
  exact_mod_cast h1.trans h2

end Sensitivity

end Frontier

