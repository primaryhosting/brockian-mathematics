/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- The Boolean core of the argument: for any five colours `a, b, c, d, e`
(the colours of `1, 2, 3, 4, 5`), at least one of the six equations
`1 + 1 = 2`, `1 + 2 = 3`, `1 + 3 = 4`, `1 + 4 = 5`, `2 + 2 = 4`, `2 + 3 = 5`
is monochromatic. Verified by exhausting the `32` colourings. -/

private theorem schur_five_bool (a b c d e : Bool) :
    (a = a ∧ a = b) ∨ (a = b ∧ b = c) ∨ (a = c ∧ c = d) ∨ (a = d ∧ d = e) ∨
      (b = b ∧ b = d) ∨ (b = c ∧ c = e) := by
  revert a b c d e
  decide

/-- **Schur's theorem, the instance `S(2) < 5`.**

For every `2`-colouring `f` of `{1, 2, 3, 4, 5}` — encoded as `f : Fin 5 → Bool`,
where the index `i` stands for the number `i + 1` — there is a monochromatic
Schur triple: elements `x`, `y`, `z` of `{1, …, 5}` with `x + y = z` and
`f x = f y = f z`. (Here `x = y` is allowed, as in the usual definition of a
sum-free set.) -/
