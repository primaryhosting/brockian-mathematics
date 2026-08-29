import Mathlib

/-!
# The rays of a three dimensional Kochen–Specker configuration

The 33 rays of a Kochen–Specker configuration in `ℝ³` (coordinates in `{0, ±1, ±√2}`),
together with the auxiliary vectors completing each orthogonal pair to a frame, and the
boolean bookkeeping lemmas used in the case analysis.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
namespace KS3

/-- The three dimensional real Hilbert space. -/
abbrev V3 := EuclideanSpace ℝ (Fin 3)


def u18 : KSSpace := !₂[(-1:ℝ), 1, 1, 1]

end KS

/--
**Kochen–Specker theorem** (base case, dimension four).

There is no `{0,1}`-valued (noncontextual) assignment `f` on the vectors of a four dimensional
real Hilbert space with the property that in every orthogonal frame (four pairwise orthogonal
nonzero vectors) exactly one vector is assigned the value `1`.

The proof uses the 18-vector, 9-basis Kochen–Specker set of Cabello, Estebaranz and
García-Alcaine: each of the 18 vectors occurs in exactly two of the 9 bases, so summing the
nine "exactly one" constraints gives `9 = 2 * (number of vectors assigned 1)`, which is
impossible by parity.
-/
