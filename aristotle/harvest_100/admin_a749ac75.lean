/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace AdditiveComb

/-- **Schur's theorem, the instance `S(2) < 5`.**

For every 2-colouring `f` of `{1, 2, 3, 4, 5}` — encoded as `f : Fin 5 → Bool`, where the
index `i : Fin 5` represents the integer `i + 1` — there is a monochromatic Schur triple:
elements `x, y, z` of `{1, …, 5}` with `x + y = z` and `f x = f y = f z`.
Here `x` and `y` are not required to be distinct.

The proof is a finite case analysis on the five colours `f 0, …, f 4`: in each of the
32 cases one of the six Schur triples `1+1=2`, `1+2=3`, `1+3=4`, `2+2=4`, `1+4=5`, `2+3=5`
is monochromatic.

(This file needs no `import`, since the statement and its case analysis use only `Fin`,
`Bool` and `Nat`; Lean requires `import` lines to precede all other content, so keeping the
file import-free lets the prescribed header comment stand at the very top.) -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      (x.val + 1) + (y.val + 1) = (z.val + 1) ∧ f x = f y ∧ f y = f z := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;> cases h4 : f 4 <;>
  first
    | exact ⟨0, 0, 1, rfl, rfl, h0.trans h1.symm⟩
    | exact ⟨0, 1, 2, rfl, h0.trans h1.symm, h1.trans h2.symm⟩
    | exact ⟨0, 2, 3, rfl, h0.trans h2.symm, h2.trans h3.symm⟩
    | exact ⟨1, 1, 3, rfl, rfl, h1.trans h3.symm⟩
    | exact ⟨0, 3, 4, rfl, h0.trans h3.symm, h3.trans h4.symm⟩
    | exact ⟨1, 2, 4, rfl, h1.trans h2.symm, h2.trans h4.symm⟩

end AdditiveComb

