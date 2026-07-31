import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import no_theater_lint as lint  # noqa: E402


def modes(findings):
    return {f.mode for f in findings}


def test_clean_file_no_findings():
    text = "import Mathlib\ntheorem t : 1 + 1 = 2 := by decide\n"
    assert lint.lint_text("Core.lean", text, set()) == []


def test_flags_r_mod_collapse():
    text = "def goldenPhase (x : ℝ) : ℝ := x % (2 * π)\n"
    assert "r_mod_collapse" in modes(lint.lint_text("X.lean", text, set()))


def test_flags_nat_div_exponent():
    text = "theorem bad : x ^ (1 / 2) ≤ y := sorry\n"
    assert "nat_div_exponent" in modes(lint.lint_text("X.lean", text, set()))


def test_flags_placeholder_zero_operator():
    text = "def laplacian : H →L[ℂ] H := 0  -- Laplacian placeholder\n"
    assert "placeholder_zero" in modes(lint.lint_text("X.lean", text, set()))


def test_hole_is_blocking_only_in_closed_module():
    text = "theorem t : True := by sorry\n"
    open_find = lint.lint_text("SpectralGate1.lean", text, closed=set())
    closed_find = lint.lint_text("Core.lean", text, closed={"Core"})
    assert any(f.mode == "hole" and not f.blocking for f in open_find)
    assert any(f.mode == "hole" and f.blocking for f in closed_find)


def test_sorry_in_comment_not_flagged_as_hole():
    text = "theorem t : True := trivial  -- no sorry here, honest\n"
    assert not any(f.mode == "hole" for f in lint.lint_text("Core.lean", text, {"Core"}))


def test_sorry_in_block_docstring_not_flagged():
    text = ('/-- Ported (the legacy source left this as `sorry`); discharged via Mathlib. -/\n'
            'theorem binet : True := trivial\n')
    assert not any(f.mode == "hole" for f in lint.lint_text("Core.lean", text, {"Core"}))


def test_real_sorry_still_flagged_after_docstring():
    text = ('/-- mentions sorry in doc -/\n'
            'theorem t : True := by sorry\n')
    holes = [f for f in lint.lint_text("Core.lean", text, {"Core"}) if f.mode == "hole"]
    assert len(holes) == 1 and holes[0].line == 2 and holes[0].blocking
