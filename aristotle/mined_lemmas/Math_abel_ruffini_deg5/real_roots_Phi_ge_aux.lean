/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`, so the header
-- above is a plain comment and is repeated verbatim as a module docstring after the import.)

/-
The argument below is the classical Galois-theoretic proof of the Abel-Ruffini theorem
in degree 5, following the treatment of `Archive/Wiedijk100Theorems/AbelRuffini.lean`
in mathlib4 (author: Thomas Browning, Apache 2.0).  It is reproduced here in
self-contained form because the mathlib `Archive` library is not imported by default.

The key mathlib ingredients are:
* `solvableByRad.isSolvable'`  (an irreducible polynomial with a root solvable by radicals
  has solvable Galois group);
* `Polynomial.Gal.galActionHom_bijective_of_prime_degree'`  (an irreducible polynomial of
  prime degree with 1-3 non-real roots has full Galois group);
* `Equiv.Perm.not_solvable`  (the symmetric group on 5 letters is not solvable).
-/

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

namespace AbelRuffiniQuintic

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`. -/

theorem real_roots_Phi_ge_aux (hab : b < a) :
    ∃ x y : ℝ, x ≠ y ∧ aeval x (Phi ℚ a b) = 0 ∧ aeval y (Phi ℚ a b) = 0 := by
  let f : ℝ → ℝ := fun x : ℝ => aeval x (Phi ℚ a b)
  have hf : f = fun x : ℝ => x ^ 5 - a * x + b := by simp [f, Phi]
  have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (Phi ℚ a b).continuousOn_aeval
  have ha : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr (Nat.one_le_of_lt hab)
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hf0 : 0 ≤ f 0 := by simp [hf]
  by_cases hb : (1 : ℝ) - a + b < 0
  · have hf1 : f 1 < 0 := by simp [hf, hb]
    have hfa : 0 ≤ f a := by
      simp_rw [hf, ← sq]
      refine add_nonneg (sub_nonneg.mpr (pow_right_mono₀ ha ?_)) ?_ <;> norm_num
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' hle (hc _) (Set.mem_Ioc.mpr ⟨hf1, hf0⟩)
    obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc ha (hc _) (Set.mem_Ioc.mpr ⟨hf1, hfa⟩)
    exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩
  · replace hb : (b : ℝ) = a - 1 := by linarith [show (b : ℝ) + 1 ≤ a from mod_cast hab]
    have hf1 : f 1 = 0 := by simp [hf, hb]
    have hfa :=
      calc
        f (-a) = (a : ℝ) ^ 2 - (a : ℝ) ^ 5 + b := by
          norm_num [hf, ← sq, sub_eq_add_neg, add_comm, Odd.neg_pow (by decide : Odd 5)]
        _ ≤ (a : ℝ) ^ 2 - (a : ℝ) ^ 3 + (a - 1) := by gcongr <;> linarith
        _ = -((a : ℝ) - 1) ^ 2 * (a + 1) := by ring
        _ ≤ 0 := by nlinarith
    have ha' := neg_nonpos.mpr (hle.trans ha)
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Icc ha' (hc _) (Set.mem_Icc.mpr ⟨hfa, hf0⟩)
    exact ⟨x, 1, (hx1.trans_lt zero_lt_one).ne, hx2, hf1⟩

