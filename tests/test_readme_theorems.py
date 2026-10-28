"""The README's theorem tables against the pinned statements.

scripts/audit.sh ties the published theorems to scripts/statements.expected, but it never reads the
README. Here the theorem names in the tables under "What is proven" must be exactly the names of
the STATEMENT lines in scripts/statements.expected. So a theorem renamed in the README, dropped from
the pins (and from the audit's list, which keeps the audit green) or pinned without a row fails. A
row whose statement says "iff" must name a theorem pinned with `↔`. Reads two text files: needs no
binary and no Lean.

What counts as a name: in a table whose first header cell is "Theorem", each code span of a row's
first cell. A span must be a Lean name, and the cell may hold nothing else but commas, "and",
emphasis and links around a name, so that no name can be written where it is not read. Code in the
other columns (`check`, `p`, `64:ff9b::/96`, a theorem mentioned in passing) is never taken for a
name. Names are relative to the `UrlFence` namespace, and after a line of the section that says
"namespace `…`" (the line before the address table: `UrlFence.Addr`), to that one. Tables in fenced
code blocks are ignored, and any other table in the section fails.
"""
import os
import re
import unittest

from common import ROOT

NAMESPACE = "UrlFence"
SECTION = "What is proven"

HEADING = re.compile(r" {0,3}(#{1,6})[ \t]+(.*?)(?:[ \t]+#+)?[ \t]*\Z")
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")
DELIMITER_ROW = re.compile(r"[ \t]*\|?[ \t]*:?-+:?[ \t]*(?:\|[ \t]*:?-+:?[ \t]*)*\|?[ \t]*\Z")
CODE = re.compile(r"`([^`]*)`")
LINK = re.compile(r"\[([^\]]*)\]\([^)]*\)")
NAME = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*\Z")
SEPARATORS = re.compile(r"(?:[\s,*]|\band\b)*\Z")
NAMESPACE_LINE = re.compile(r"\bnamespace `([^`]*)`")
IFF = re.compile(r"\biff\b")


def read(*path):
    with open(os.path.join(ROOT, *path), encoding="utf-8") as f:
        return f.read()


def pinned_statements(expected):
    """{full name: statement} for the STATEMENT lines of scripts/statements.expected."""
    return dict(re.findall(r"^STATEMENT (\S+) : (.*)$", expected, re.M))


def cells(line):
    """The cells of a table row, split at each `|` not written as `\\|`."""
    line = line.strip()
    parts = re.split(r"(?<!\\)\|", line)
    if line.startswith("|"):
        parts = parts[1:]
    if line.endswith("|") and not line.endswith("\\|"):
        parts = parts[:-1]
    return [p.strip() for p in parts]


def theorem_rows(readme):
    """The rows of the tables under the SECTION heading, up to the next heading of the same or a
    higher level, as (line number, full theorem names, statement text). Raises ValueError for a
    table or a first cell this test cannot read."""
    lines = readme.splitlines()
    rows, level, namespace, fence, in_table = [], None, NAMESPACE, None, False
    for i, line in enumerate(lines):
        where = f"README.md:{i + 1}"
        if fence:
            if line.strip().startswith(fence):
                fence = None
            continue
        f = FENCE.match(line)
        if f:
            fence, in_table = f.group(1), False
            continue
        h = HEADING.match(line)
        if h and level is not None and len(h.group(1)) <= level:
            break
        if h and h.group(2) == SECTION:
            level = len(h.group(1))
        if h or level is None:
            in_table = False
            continue
        if not line.strip():
            in_table = False
        elif in_table:
            row = cells(line) or [""]
            first = LINK.sub(r"\1", row[0])
            names = CODE.findall(first)
            if not names or not all(NAME.match(n) for n in names) or not SEPARATORS.match(CODE.sub("", first)):
                raise ValueError(f"{where}: the first cell should list theorem names in backticks: {row[0]!r}")
            rows.append((i + 1, [f"{namespace}.{n}" for n in names], " | ".join(row[1:])))
        elif "|" in line and DELIMITER_ROW.match(line):
            if cells(lines[i - 1])[:1] != ["Theorem"]:
                raise ValueError(f"{where}: a table under {SECTION!r} with header {lines[i - 1].strip()!r}; "
                                 "its first column must be 'Theorem'")
            in_table = True
        else:
            m = NAMESPACE_LINE.search(line)
            if m:
                namespace = m.group(1)
                if namespace != NAMESPACE and not namespace.startswith(NAMESPACE + "."):
                    raise ValueError(f"{where}: namespace {namespace!r} is not inside {NAMESPACE}")
    if level is None:
        raise ValueError(f"README.md has no heading {SECTION!r}")
    return rows


class ReadmeTheorems(unittest.TestCase):
    def load(self):
        try:
            rows = theorem_rows(read("README.md"))
        except ValueError as e:
            self.fail(str(e))
        pinned = pinned_statements(read("scripts", "statements.expected"))
        self.assertTrue(pinned, "scripts/statements.expected has no STATEMENT line")
        return rows, pinned

    def test_tables_name_exactly_the_pinned_theorems(self):
        rows, pinned = self.load()
        named = {n for _, names, _ in rows for n in names}
        diff = []
        if named - pinned.keys():
            diff.append("in a README table, not pinned in scripts/statements.expected: "
                        + ", ".join(sorted(named - pinned.keys())))
        if pinned.keys() - named:
            diff.append("pinned in scripts/statements.expected, in no README table: "
                        + ", ".join(sorted(pinned.keys() - named)))
        if diff:
            self.fail("\n".join(diff))

    def test_iff_rows_name_an_equivalence(self):
        rows, pinned = self.load()
        iff_rows = [(n, names) for n, names, statement in rows if IFF.search(CODE.sub("", statement))]
        self.assertTrue(iff_rows, 'no row says "iff"; has the table changed?')
        # A row with no pinned name at all is reported by the test above.
        bad = [f"README.md:{n}: says iff, but none of {', '.join(names)} is pinned with ↔"
               for n, names in iff_rows
               if any(x in pinned for x in names) and not any("↔" in pinned.get(x, "") for x in names)]
        if bad:
            self.fail("\n".join(bad))


if __name__ == "__main__":
    unittest.main()
