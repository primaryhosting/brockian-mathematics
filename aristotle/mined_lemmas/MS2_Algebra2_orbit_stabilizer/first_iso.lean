import Mathlib
namespace MS2.Algebra2

theorem first_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty ((G ⧸ f.ker) ≃* f.range) :=
  ⟨QuotientGroup.quotientKerEquivRange f⟩
end MS2.Algebra2

