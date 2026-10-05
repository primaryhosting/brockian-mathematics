/- (Lean requires `import` to be the first command, so this header is written as a plain
block comment; the module docstring `/-! ... -/` with the same content follows the imports.)
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix

namespace Chem

/-- Adjacency matrix of the cycle graph `C₄`: vertices are `Fin 4` (i.e. `ℤ/4ℤ`) and
`i` is adjacent to `j` exactly when `i - j = ±1` modulo `4`. -/

theorem range_two_cos : (Set.range fun k : Fin 4 => 2 * Real.cos (2 * Real.pi * k / 4))
    = ({2, 0, -2} : Set ℝ) := by
  have c1 : Real.cos (2 * Real.pi / 4) = 0 := by
    rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring]; exact Real.cos_pi_div_two
  have c2 : Real.cos (2 * Real.pi * 2 / 4) = -1 := by
    rw [show 2 * Real.pi * 2 / 4 = Real.pi by ring]; exact Real.cos_pi
  have c3 : Real.cos (2 * Real.pi * 3 / 4) = 0 := by
    rw [show 2 * Real.pi * 3 / 4 = Real.pi + Real.pi / 2 by ring, Real.cos_add]; simp
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num
    · right; left; norm_num [c1]
    · right; right; norm_num [c2]
    · right; left; norm_num [c3]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num [c1]⟩
    · exact ⟨2, by norm_num [c2]⟩

/-- **Hückel theory for cyclobutadiene (C₄).**  The eigenvalues of the adjacency matrix of the
cycle graph `C₄` are exactly the numbers `2 cos (2πk/4)` for `k = 0, 1, 2, 3`
(namely `2, 0, 0, -2`). -/
