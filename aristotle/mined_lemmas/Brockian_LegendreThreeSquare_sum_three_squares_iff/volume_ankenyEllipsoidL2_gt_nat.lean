import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma volume_ankenyEllipsoidL2_gt_nat (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (16 * n * q : ℝ≥0∞) < volume (ankenyEllipsoidL2 (n : ℝ) (q : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h :=
    volume_ankenyEllipsoidL2_gt (n := (n : ℝ)) (q := (q : ℝ)) hnR hqR
  -- `ENNReal.ofReal (16*(n*q))` is definitionally the same as the `ℝ≥0∞` nat-cast here.
  -- (The casts and `ofReal` normalizations are handled by `simp`.)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-!
## The “computable covolume” kernel for the Ankeny lattice

In Ankeny’s proof we want a full-rank ℤ-lattice inside `E3` with *explicitly computable covolume*.

Rather than trying to compute the covolume of the congruence-defined lattice `ankeny_lattice` directly,
we build an explicit ℤ-span lattice from a concrete ℝ-basis and compute the fundamental-domain volume via
`ZSpan.volume_fundamentalDomain` (determinant).
-/

/-- A concrete ℝ-basis whose ℤ-span has covolume `2*n*q`.

The associated matrix (with basis vectors as columns) is:

```text
[ n    2q   b ]
| 0    2q   b |
[ 0     0   1 ]
```

so `det = 2*n*q`. -/
