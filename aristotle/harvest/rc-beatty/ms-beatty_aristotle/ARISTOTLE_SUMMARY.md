# Summary of changes for run 11b9ebe2-7172-4e28-b861-01dbb05ebb8f
`Beatty.lean` now contains a complete proof of the Rayleigh–Beatty theorem, with the `sorry` removed. The theorem statement is unchanged from the original:

for `r s : ℝ` with `1 < r`, `Irrational r`, `1/r + 1/s = 1`, and `n : ℕ` with `0 < n`,
`(∃ m : ℕ, 0 < m ∧ ⌊m·r⌋ = n) ↔ ¬(∃ m : ℕ, 0 < m ∧ ⌊m·s⌋ = n)`.

Structure of the proof (two small private helper lemmas plus the main argument, all in the `Brockian.MsBeatty` namespace):
- `holderConj_of`: `1 < r` together with `1/r + 1/s = 1` gives `r.HolderConjugate s`.
- `mem_beatty_iff`: membership in the positive Beatty set is equivalent to the natural-number-indexed form used in the statement.
- The main theorem combines these with Mathlib's `Irrational.beattySeq_symmDiff_beattySeq_pos` (the symmetric-difference form of Rayleigh's theorem in the root Mathlib namespace) applied at `n`, and extracts the exclusive-or into the stated iff.

Verification: the file builds against a bare `import Mathlib` with no errors; a search confirms no `sorry`, `admit`, or `native_decide` remains; and an axiom check on `Brockian.MsBeatty.beatty` reports only `propext`, `Classical.choice`, and `Quot.sound`. No Archive or other non-core namespaces are used. All work is committed and pushed.