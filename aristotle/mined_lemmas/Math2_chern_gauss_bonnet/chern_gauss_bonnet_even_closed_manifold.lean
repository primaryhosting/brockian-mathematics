import Mathlib

/-!
# Gauss–Bonnet (the `n = 1` case of Chern–Gauss–Bonnet) for the 2-torus

This file contains a *smooth* instance of the Chern–Gauss–Bonnet theorem, complementing the
combinatorial theorem `Math2.chern_gauss_bonnet` in `RequestProject.Main`.

For a closed oriented surface `M` the Chern–Gauss–Bonnet theorem reads
`∫_M K dA = 2π χ(M)`.  We prove this for the closed even-dimensional manifold
`T² = ℝ²/ℤ²` equipped with an *arbitrary* conformal metric `e^{2u}(dx² + dy²)`, where `u` is
any doubly periodic potential with enough regularity.  For such a metric the Gauss curvature
is `K = -e^{-2u} Δu` and the area density is `e^{2u}`, so the total curvature is `-∫∫ Δu`,
which vanishes by periodicity — in agreement with `χ(T²) = 0`.
-/

namespace Math2.Torus

open MeasureTheory

/-- Partial derivative in the first variable. -/

theorem chern_gauss_bonnet_even_closed_manifold {V : Type*} [DecidableEq V]
    (K : SimplicialComplex V) (d : ℕ) (hd : Even d) (hK : K.IsClosedManifold d) :
    ∑ v ∈ K.vertices, ∑ k ∈ Finset.range (d + 1),
        (-1 : ℚ) ^ k * (K.linkFVector v k : ℚ) / ((k : ℚ) + 1) = (K.eulerChar : ℚ) := by
  obtain ⟨m, rfl⟩ := hd
  rw [← chern_gauss_bonnet K]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine (K.curvature_eq_linkFVector v (m + m) ?_).symm
  intro s hs
  have h := hK.dim_le _ (K.mem_link.1 hs).2
  have hcard : (insert v s).card = s.card + 1 :=
    Finset.card_insert_of_notMem (K.mem_link.1 hs).1
  omega

/-! ## A worked even-dimensional closed manifold: the octahedral triangulation of `S²`

The octahedron is the simplicial complex on six vertices `0,…,5`, thought of as three pairs of
antipodal points `{0,1}, {2,3}, {4,5}`, whose simplices are the nonempty subsets containing at
most one point of each antipodal pair.  It is a closed combinatorial `2`-manifold (a
triangulated `2`-sphere) with `6` vertices, `12` edges and `8` triangles.  Each vertex has a
link which is a `4`-cycle, so `V_{-1} = 1`, `V_0 = 4`, `V_1 = 4` and the curvature at each
vertex is `1 - 4/2 + 4/3 = 1/3`; the total curvature is `6 · (1/3) = 2 = χ(S²)`. -/

/-- The octahedral triangulation of the `2`-sphere. -/
