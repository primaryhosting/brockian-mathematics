import struct
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from fetch_zeta_zeros import parse_zeros_text, validate_zeros, encode_f64le

SAMPLE = """14.134725141734693790
21.022039638771554993
25.010857580145688763
"""


def test_parse_zeros_text():
    zeros = parse_zeros_text(SAMPLE)
    assert zeros == pytest.approx(
        [14.134725141734694, 21.022039638771555, 25.010857580145689], abs=1e-12)


def test_parse_skips_blank_lines():
    assert len(parse_zeros_text("14.1\n\n21.0\n")) == 2


def test_validate_accepts_increasing_positive():
    # first value must be the real first zero — validate_zeros checks it to 1e-6
    validate_zeros([14.134725141734693, 21.02, 25.01], expected_count=3)  # no raise


def test_validate_rejects_wrong_count():
    with pytest.raises(ValueError, match="expected 5"):
        validate_zeros([14.13, 21.02], expected_count=5)  # count check fires first


def test_validate_rejects_non_increasing():
    with pytest.raises(ValueError, match="increasing"):
        validate_zeros([14.134725141734693, 14.134725141734693, 25.01],
                       expected_count=3)


def test_validate_rejects_bad_first_zero():
    with pytest.raises(ValueError, match="first zero"):
        validate_zeros([1.0, 2.0], expected_count=2)


def test_encode_f64le_roundtrip():
    vals = [14.134725141734694, 21.022039638771555]
    blob = encode_f64le(vals)
    assert len(blob) == 16
    assert list(struct.unpack("<2d", blob)) == vals
