import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem zeta_pow_mod {p : ℕ} {ζ : F} (hζp : ζ ^ p = 1) (j : ℕ) : ζ ^ j = ζ ^ (j % p) := by
  conv_lhs => rw [← Nat.div_add_mod j p]
  rw [pow_add, pow_mul, hζp, one_pow, one_mul]

/-- Interpolation: the `p`-th root of unity power `ζ ^ w` is a combination of the indicators
of `w + a ≡ 0 mod p`. -/
