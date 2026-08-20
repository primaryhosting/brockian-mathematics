/-
# The infinite Ramsey theorem

Mathlib (as of this project's pinned version) contains no form of Ramsey's theorem, so we develop
the infinite version here, for colourings of `n`-element subsets of `ℕ` with `k` colours.

An infinite homogeneous set is presented as the range of a strictly monotone function `f : ℕ → ℕ`.
-/
import Mathlib

set_option autoImplicit false

namespace Frontier

open Finset

/-- `Homogeneous n c f a` says that every `n`-element subset of the range of `f` has colour `a`. -/

lemma exists_limit_coloring {k : ℕ} (U : Ultrafilter ℕ) (F : ℕ → Finset ℕ → Fin k) :
    ∃ c : Finset ℕ → Fin k, ∀ s : Finset ℕ, {N | F N s = c s} ∈ U := by
  have key : ∀ s : Finset ℕ, ∃ b : Fin k, ∀ᶠ N in (U : Filter ℕ), F N s = b := fun s =>
    Ultrafilter.eventually_exists_iff.mp (Filter.Eventually.of_forall fun N => ⟨F N s, rfl⟩)
  choose c hc using key
  exact ⟨c, hc⟩

/-- Finitely many of the ultrafilter conditions can be met simultaneously. -/
