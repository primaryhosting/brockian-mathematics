import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

lemma rank_pos_of_ne_zero [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (hM : M ≠ 0) : 0 < M.rank := by
  rcases Nat.eq_zero_or_pos M.rank with h | h
  · exfalso
    have hbot : LinearMap.range M.mulVecLin = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; exact h
    apply hM
    ext x y
    have hzero : M.mulVecLin (Pi.single y 1) = 0 := by
      have := LinearMap.range_eq_bot.mp hbot
      simp [this]
    have := congrFun hzero x
    simpa [mulVecLin_apply, mulVec_single] using this
  · exact h

end RankTools


section CoreLemma

variable {A B C : Type*}

open ComplexConjugate

/-- **Core decoupling lemma.**
If a four-party tensor `f : R → A → B → C → ℂ` has the property that the `R`-`A` marginal
and the `R`-`B` marginal both factorize (the `R` register is decoupled from `A`, and from `B`),
then `card R ≤ card C`. -/
