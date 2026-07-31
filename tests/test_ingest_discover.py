import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import ingest_discover  # noqa: E402


def test_dedup_by_md5(tmp_path):
    (tmp_path / "a.lean").write_text("theorem t : True := trivial\n")
    (tmp_path / "b.lean").write_text("theorem t : True := trivial\n")  # identical
    (tmp_path / "c.lean").write_text("theorem u : 1 = 1 := rfl\n")  # distinct
    (tmp_path / "note.md").write_text("not lean\n")  # ignored

    sources = ingest_discover.discover([str(tmp_path)])
    assert len(sources) == 2
    dup = next(s for s in sources if len(s.paths) == 2)
    assert {os.path.basename(p) for p in dup.paths} == {"a.lean", "b.lean"}


def test_skips_lake_and_mathlib(tmp_path):
    keep = tmp_path / "Keep.lean"
    keep.write_text("theorem k : True := trivial\n")
    vendored = tmp_path / ".lake" / "packages" / "mathlib"
    vendored.mkdir(parents=True)
    (vendored / "Vendored.lean").write_text("theorem v : True := trivial\n")

    sources = ingest_discover.discover([str(tmp_path)])
    names = {os.path.basename(p) for s in sources for p in s.paths}
    assert names == {"Keep.lean"}
