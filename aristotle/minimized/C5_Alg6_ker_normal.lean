import Mathlib
namespace C5.Alg6

/-- The kernel of a group homomorphism is a normal subgroup. -/

theorem ker_normal {G H : Type*} [Group G] [Group H] (f : G →* H) : (f.ker).Normal :=
  inferInstance

/-- Lagrange's theorem: the index of a subgroup times its cardinality is the
cardinality of the group. -/
