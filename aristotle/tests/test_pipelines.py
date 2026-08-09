"""Unit tests for the Aristotle proof-fleet pipeline logic (pure functions / regexes).
No network, no lake. Run: python3 -m pytest aristotle/tests/ -q"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import lemma_mine  # noqa: E402
import minimize_proofs  # noqa: E402
import night_submit  # noqa: E402
import reduction_tracker  # noqa: E402
import strategy  # noqa: E402


# --- strategy diversification ---
def test_strategy_attempt0_plain_then_varies():
    assert strategy.pick(0) == ""
    assert strategy.pick(1) and strategy.pick(1) != strategy.pick(2)
    # cycles and never crashes for large attempt counts
    assert strategy.pick(999) in strategy.STRATEGIES


# --- uuid / rate-limit capture (the truncated-id bug guard) ---
def test_uuid_regex_full_only():
    full = "created project 9e035550-eb26-4d2d-809f-9034111504f3 ok"
    trunc = "error f65d5331-8e90 partial"
    assert night_submit.UUID.search(full).group(0) == "9e035550-eb26-4d2d-809f-9034111504f3"
    assert night_submit.UUID.search(trunc) is None      # must NOT accept a truncated id


def test_rate_limit_detected():
    assert night_submit.RATE.search("HTTP 429 Too Many Requests")
    assert night_submit.RATE.search("rate limit exceeded")
    assert not night_submit.RATE.search("project created")


# --- lemma mining: split + sorry exclusion ---
LEAN = """import Mathlib
namespace Demo
lemma clean_one : True := trivial
lemma dirty_two : True := by sorry
"""


def test_split_decls_header_and_blocks():
    header, blocks = lemma_mine.split_decls(LEAN)
    assert "import Mathlib" in header
    assert len(blocks) == 2
    assert any("clean_one" in b[0] for b in blocks)


def test_bad_regex_flags_sorry_not_clean():
    assert lemma_mine.BAD.search("proof := by sorry")
    assert not lemma_mine.BAD.search("proof := trivial")


# --- minimizer: dead-declaration elimination ---
MINI = """import Mathlib
lemma helperA : True := trivial
lemma unusedB : True := trivial
theorem main_thm : True := helperA
"""


def test_minimize_drops_unreferenced_keeps_deps():
    out, nblocks, nkept = minimize_proofs.minimize(MINI, "main")
    assert nblocks == 3 and nkept == 2
    assert "helperA" in out and "main_thm" in out and "unusedB" not in out


def test_minimize_no_prune_when_all_used():
    text = "import Mathlib\ntheorem only_thm : True := trivial\n"
    out, nblocks, nkept = minimize_proofs.minimize(text, "only")
    assert nblocks == nkept == 1


# --- reduction tracker: detect conditional reductions ---
def test_reduction_decl_regex_matches_conditional():
    text = "theorem twin_of_hyp (h : H) : TwinPrimeConjecture := by exact foo h :="
    m = reduction_tracker.DECL.search(text)
    assert m and m.group(1) == "twin_of_hyp"
