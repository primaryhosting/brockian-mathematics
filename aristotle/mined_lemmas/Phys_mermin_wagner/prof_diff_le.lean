/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

lemma prof_diff_le {R : ℕ} (hR : 1 ≤ R) {a b : ℕ} (hab : b ≤ a + 1) (hba : a ≤ b + 1) :
    |prof R a - prof R b| ≤ 1 / (((max a 1 : ℕ) : ℝ) * harm R) := by
  have hH := harm_pos hR
  rcases Nat.lt_trichotomy a b with h | h | h
  · -- b = a + 1
    have hb : b = a + 1 := by omega
    subst hb
    have h1 : 0 ≤ prof R a - prof R (a + 1) :=
      sub_nonneg.mpr (prof_antitone (Nat.le_succ a))
    rw [abs_of_nonneg h1]
    refine le_trans (prof_step hR a) ?_
    have hmax : ((max a 1 : ℕ) : ℝ) ≤ (a + 1 : ℝ) := by
      have : (max a 1 : ℕ) ≤ a + 1 := by omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < ((max a 1 : ℕ) : ℝ) := by
      have : 1 ≤ (max a 1 : ℕ) := by omega
      have : (1 : ℝ) ≤ ((max a 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_right hmax hH.le
  · subst h
    simp
    positivity
  · -- a = b + 1
    have ha : a = b + 1 := by omega
    subst ha
    have h1 : 0 ≤ prof R b - prof R (b + 1) :=
      sub_nonneg.mpr (prof_antitone (Nat.le_succ b))
    rw [abs_of_nonpos (by linarith), neg_sub]
    refine le_trans (prof_step hR b) ?_
    have hmax : ((max (b + 1) 1 : ℕ) : ℝ) = (b + 1 : ℝ) := by
      have : (max (b + 1) 1 : ℕ) = b + 1 := by omega
      rw [this]
      push_cast
      ring
    rw [hmax]

end

end Phys

/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a Lean module docstring just below the imports, since
Lean 4 does not permit a docstring comment to precede the import commands.)
-/
import RequestProject.Profile

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open MeasureTheory Real Filter

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Phys

noncomputable section

/-! ### The classical XY model in a box of `ℤ^d` -/

/-- The nearest–neighbour bonds of the box: a bond is a pair `(x, i)` where the bond joins
`x` to `x + e_i`, and it is present when `x + e_i` still lies in the box. -/
