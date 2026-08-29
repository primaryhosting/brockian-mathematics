import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem treeLe_total (w : α → ℝ) (a b : HTree α) : (treeLe w a b || treeLe w b a) = true := by
  simp only [treeLe, Bool.or_eq_true, decide_eq_true_eq]
  exact le_total _ _

/-- One step of Huffman's algorithm: combine two trees of least weight. -/
