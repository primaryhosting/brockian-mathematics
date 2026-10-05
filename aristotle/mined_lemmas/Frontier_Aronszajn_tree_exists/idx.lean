/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

noncomputable def idx (l ξ : Ordinal) : ℕ := sInf {n | ξ < cseq l (n + 1)}

/-- The coherent sequence of finite-to-one functions.  `E o` is (on `Set.Iio o`) a
finite-to-one function to `ℕ`, and for `β < o` it agrees with `E β` on `Set.Iio β`
up to a finite set. -/
