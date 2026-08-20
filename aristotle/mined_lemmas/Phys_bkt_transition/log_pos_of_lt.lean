/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- Parameters of the two–dimensional XY model on a disc of radius `R`:
`J` is the spin stiffness (coupling), `kB` Boltzmann's constant and `a` the
short–distance cutoff (lattice spacing / vortex core size). -/
structure XYParams where
  /-- spin stiffness -/
  J : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- short distance cutoff (core radius) -/
  a : ℝ
  hJ : 0 < J
  hkB : 0 < kB
  ha : 0 < a

/-- Energy of a single vortex (topological defect of winding number `±1`) in a
system of linear size `R`: `E = π J log (R / a)`. -/

lemma log_pos_of_lt (p : XYParams) {R : ℝ} (hR : p.a < R) : 0 < Real.log (R / p.a) := by
  have ha := p.ha
  exact Real.log_pos (by rw [lt_div_iff₀ ha]; linarith)

/--
**Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

For a system of linear size `R` larger than the vortex core size `a`, the free
energy `F = E - T S` of a single topological defect (vortex) is

  `F(T, R) = (π J - 2 kB T) log (R / a)`,

which changes sign exactly at the critical temperature `T_BKT = π J / (2 kB)`:

* below `T_BKT` the free energy of an isolated vortex is strictly positive, and
  diverges as `R → ∞`, so isolated vortices are suppressed: vortices only occur
  in bound vortex–antivortex pairs (quasi–long-range ordered phase);
* at `T = T_BKT` the energetic and entropic contributions cancel exactly;
* above `T_BKT` the free energy is strictly negative and diverges to `-∞`, so
  the spontaneous creation of free vortices is favourable: the pairs unbind
  (disordered phase).

Moreover the sign of `F` is monotone (strictly decreasing) in `T`, so `T_BKT`
is the unique such transition point.
-/
