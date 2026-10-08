#!/usr/bin/env python3
"""trust-ledger: a Merkle ledger of the evidence behind a paper's claims.

Single file, Python >= 3.11, standard library only. Normative format: docs/FORMAT.md.

  ledger.py [-C DIR] status [--strict]   table of claims: Lean/ProVerif status, attestation, register size
  ledger.py [-C DIR] why CLAIM           everything CLAIM rests on, and who attested what
  ledger.py [-C DIR] lock                recompute and write ledger/lock.json (prints the root)
  ledger.py [-C DIR] verify              recompute and compare with lock.json; exit 1 on any difference
  ledger.py [-C DIR] attest CLAIM --person P --level green|yellow|conjecture [--reason R] [--checklist A1,A2]
  ledger.py [-C DIR] extract             run the configured extractor(s) (writes the Lean/ProVerif dumps)

DIR is the project root; it must contain ledger/ledger.toml.
"""
import argparse, base64, datetime, hashlib, json, os, re, shutil, subprocess, sys, tempfile, tomllib, unicodedata
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEVELS = ("green", "yellow", "conjecture")
ROOT_KINDS = ("claim", "attestation", "environment", "paper-source", "hypothesis")
ASSESSMENT_VERDICTS = ("consistent", "partial", "check", "mismatch", "unclear")
SIG_NAMESPACE = "trust-ledger-attestation"  # ssh-keygen -Y namespace: a signature cannot be replayed elsewhere
EVIDENCE = ("E1", "E2", "E3", "E4", "E5")


# ---------------------------------------------------------------- hashing (FORMAT.md section 2)
def canon(x):
    def check(v):
        if isinstance(v, float):
            raise ValueError("floats are not allowed in hashed content")
        if isinstance(v, dict):
            for k, w in v.items():
                check(k); check(w)
        elif isinstance(v, (list, tuple)):
            for w in v:
                check(w)
    check(x)
    return json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def H(tag, x):
    return hashlib.sha256(("trust-ledger/0\0" + tag + "\0" + canon(x)).encode("utf-8")).hexdigest()


def sha_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def merkle(payload, deps, tag):
    """Hash every node of a graph. payload: id -> JSON value; deps: id -> list of ids (all ids
    must be keys of payload). Strongly connected components are hashed as one unit."""
    sccs, index, low, onstack, stack, counter = [], {}, {}, set(), [], [0]
    sys.setrecursionlimit(max(10000, 4 * len(payload)))

    def tarjan(v):
        index[v] = low[v] = counter[0]; counter[0] += 1
        stack.append(v); onstack.add(v)
        for w in deps.get(v, ()):
            if w not in index:
                tarjan(w); low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); onstack.discard(w); comp.append(w)
                if w == v:
                    break
            sccs.append(sorted(comp))  # Tarjan emits dependencies first

    for v in sorted(payload):
        if v not in index:
            tarjan(v)
    h = {}
    for comp in sccs:
        ext = sorted({d for m in comp for d in deps.get(m, ()) if d not in comp})
        extdeps = [[d, h[d]] for d in ext]
        if len(comp) == 1 and comp[0] not in deps.get(comp[0], ()):
            v = comp[0]
            h[v] = H(tag, {"p": payload[v], "deps": [[d, h[d]] for d in sorted(set(deps.get(v, ())))]})
        else:
            hc = H(tag + "-scc", {"members": [[m, payload[m]] for m in comp], "deps": extdeps})
            for m in comp:
                h[m] = H(tag + "-member", [m, hc])
    return h


# ---------------------------------------------------------------- signatures (ssh-keygen -Y)
def fingerprint(pub):
    """OpenSSH-style SHA256 fingerprint of a public key line ("ssh-ed25519 AAAA... comment")."""
    blob = base64.b64decode(pub.split()[1])
    return "SHA256:" + base64.b64encode(hashlib.sha256(blob).digest()).decode().rstrip("=")


def attestation_message(project, a):
    """The bytes that are signed: everything the attestation asserts, in canonical JSON."""
    body = {k: a.get(k, "") for k in ("claim", "hypothesis", "person", "date", "level", "reason", "bound")}
    body |= {"checklist": list(a.get("checklist", [])), "project": project}
    return ("trust-ledger/0 attestation\n" + canon(body)).encode("utf-8")


def ssh_sign(keyfile, message):
    r = subprocess.run(["ssh-keygen", "-Y", "sign", "-f", str(keyfile), "-n", SIG_NAMESPACE],
                       input=message, capture_output=True)
    if r.returncode:
        sys.exit("ssh-keygen -Y sign failed: " + r.stderr.decode(errors="replace").strip())
    return r.stdout.decode()


def ssh_verify(pub, key_id, sig, message):
    """True / False, or None when ssh-keygen is not available (signature unchecked)."""
    with tempfile.TemporaryDirectory() as d:
        allowed, sigf = Path(d) / "allowed", Path(d) / "sig"
        allowed.write_text(f'{key_id} namespaces="{SIG_NAMESPACE}" {" ".join(pub.split()[:2])}\n')
        sigf.write_text(sig)
        try:
            r = subprocess.run(["ssh-keygen", "-Y", "verify", "-f", str(allowed), "-I", key_id, "-n", SIG_NAMESPACE,
                                "-s", str(sigf)], input=message, capture_output=True)
        except FileNotFoundError:
            return None
        return r.returncode == 0


# ---------------------------------------------------------------- LaTeX: sources and statements
STATEMENT_ENVS = {"theorem", "proposition", "lemma", "corollary", "definition", "example", "remark",
                  "conjecture", "claim", "fact", "observation", "assumption", "problem"}
RESULT_ENVS = {"theorem", "proposition", "lemma", "corollary", "conjecture", "claim", "fact", "observation"}
MATH_ENVS = {"equation", "align", "gather", "multline", "eqnarray", "flalign", "alignat"}
INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")
BIB_RE = re.compile(r"\\bibliography\s*\{([^}]+)\}")
USEPACKAGE_RE = re.compile(r"\\(?:usepackage|RequirePackage)(?:\s*\[[^\]]*\])?\s*\{([^}]+)\}")
NEWTHEOREM_RE = re.compile(r"\\newtheorem\*?\{([A-Za-z]+)\}(?:\[[^\]]*\])?\{([^}]*)\}(?:\[[^\]]*\])?")
ENV_RE = re.compile(r"\\(begin|end)\{([A-Za-z]+\*?)\}")
# \newtheorem captions that classify an environment as a result (theorem-like) vs. a non-result
# statement environment (definition, example, ...); an unrecognised caption defaults to a result,
# so that an unusual name is reported as uncovered rather than silently skipped.
RESULT_CAPTION_WORDS = {"theorem", "proposition", "lemma", "corollary", "conjecture", "claim", "fact", "observation"}
NONRESULT_CAPTION_WORDS = {"definition", "example", "remark", "assumption", "problem", "criterion"}


def strip_comments(text):
    """Remove TeX comments: a % that is not preceded by an odd number of backslashes."""
    out = []
    for line in text.split("\n"):
        i = 0
        while i < len(line):
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == "%":
                line = line[:i]
                break
            i += 1
        out.append(line)
    return "\n".join(out)


def tex_sources(main, search, excluded):
    """The .tex files reached from `main` by \\input/\\include (in order), the .bib files named by
    \\bibliography, and the local .sty files named by \\usepackage/\\RequirePackage that exist next to
    the paper (packages installed in the system TeX distribution are not local and are left alone: a
    local .sty changes what a theorem statement means and so must be hashed, see docs/FORMAT.md).
    Files below an excluded directory are left out. Returns (paths, unresolved names)."""
    def resolve(name, cur, exts):  # like TeX: relative to the directory LaTeX runs in, not to `cur`
        for base in [Path(main).resolve().parent, *search]:
            for e in exts:
                cand = base / (name if (e == "" or name.endswith(e)) else name + e)
                if cand.is_file():
                    return cand.resolve()
        return None

    def is_excluded(path):
        return any(path == x or x in path.parents for x in excluded)

    files, unresolved, todo = [], [], [Path(main).resolve()]
    while todo:
        cur = todo.pop(0)
        if cur in files or is_excluded(cur):
            continue
        files.append(cur)
        if cur.suffix not in (".tex", ".sty"):
            continue
        text = strip_comments(cur.read_text(errors="replace"))
        for m in INPUT_RE.finditer(text):
            name = m.group(1).strip()
            if "\\" in name or "#" in name:  # built from macros at run time (typical inside a .sty): not resolvable statically
                continue
            r = resolve(name, cur, ("", ".tex"))
            if r is None:
                unresolved.append(name)
            else:
                todo.append(r)
        for m in BIB_RE.finditer(text):
            for name in m.group(1).split(","):
                r = resolve(name.strip(), cur, (".bib",))
                if r is None:
                    unresolved.append(name.strip() + ".bib")
                else:
                    todo.append(r)
        for m in USEPACKAGE_RE.finditer(text):
            for name in m.group(1).split(","):
                name = name.strip()
                r = name and resolve(name, cur, (".sty",))
                if r is not None:  # silently skip: most packages are not local, which is normal
                    todo.append(r)
    return files, sorted(set(unresolved))


def discover_theorem_envs(files):
    """\\newtheorem environments declared in `files` (any suffix), beyond the built-in STATEMENT_ENVS /
    RESULT_ENVS: (stmt_envs, result_envs, kind_words), to be unioned with the built-in sets per paper."""
    stmt, result, words = set(), set(), {}
    for f in files:
        text = strip_comments(f.read_text(errors="replace"))
        for m in NEWTHEOREM_RE.finditer(text):
            name, caption = m.group(1), m.group(2).strip()
            if name in STATEMENT_ENVS:
                continue
            stmt.add(name)
            cwords = re.findall(r"[A-Za-z]+", caption.lower())
            if not any(w in NONRESULT_CAPTION_WORDS for w in cwords):  # unknown caption: treat as a result
                result.add(name)
            if caption:
                words[name] = caption
    return stmt, result, words


def flatten_tex(main, search):
    """The text of `main` with every \\input/\\include replaced by the file's text, comments stripped:
    labels then appear in the order of the compiled document."""
    main = Path(main).resolve()

    def resolve(name, exts=("", ".tex")):
        for base in [main.parent, *search]:
            for e in exts:
                cand = base / (name if (e == "" or name.endswith(e)) else name + e)
                if cand.is_file():
                    return cand.resolve()
        return None

    def expand(path, stack):
        text = strip_comments(path.read_text(errors="replace"))

        def repl(m):
            r = resolve(m.group(1).strip())
            return expand(r, stack | {r}) if r and r not in stack else ""
        return INPUT_RE.sub(repl, text)
    return expand(main, {main})


def find_environments(text, extra_stmt=frozenset()):
    """Statement and display-math environments of `text`: (name, body_start, body_end). `extra_stmt`
    adds environments declared by \\newtheorem in this paper, beyond the built-in STATEMENT_ENVS."""
    stack, envs = [], []
    for m in ENV_RE.finditer(text):
        kind, name = m.group(1), m.group(2)
        base = name.rstrip("*")
        if base not in STATEMENT_ENVS and base not in extra_stmt and base not in MATH_ENVS:
            continue
        if kind == "begin":
            stack.append((name, m.end()))
        else:
            for k in range(len(stack) - 1, -1, -1):
                if stack[k][0] == name:
                    envs.append((name, stack[k][1], m.start()))
                    del stack[k:]
                    break
    return envs


def result_labels(text, envs, extra_result=frozenset()):
    """Labels whose innermost environment is a theorem-like result (not a definition, remark or equation).
    `extra_result` adds environments declared by \\newtheorem in this paper."""
    out = []
    for m in re.finditer(r"\\label\{([^}]+)\}", text):
        inner = None
        for e in envs:
            if e[1] <= m.start() < e[2] and (inner is None or e[1] > inner[1]):
                inner = e
        if inner and (inner[0].rstrip("*") in RESULT_ENVS or inner[0].rstrip("*") in extra_result):
            out.append(m.group(1))
    return out


KIND_WORDS = {"theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma", "corollary": "Corollary",
              "conjecture": "Conjecture", "claim": "Claim", "fact": "Fact", "observation": "Observation",
              "assumption": "Assumption", "problem": "Problem", "definition": "Definition", "remark": "Remark",
              "example": "Example"}


def reference_tex(label, parsed, extra_words=None):
    """How a reader cites the labelled item: 'Lemma~\\ref{l}' or 'Equation~(\\ref{l})'. The type word comes from the
    environment in the source, not from the counter (theorem-like environments often share one). `extra_words`
    supplies the \\newtheorem caption for environments beyond the built-in KIND_WORDS."""
    pat = re.compile(r"\\label\{" + re.escape(label) + r"\}")
    for text, envs in parsed:
        m = pat.search(text)
        if not m:
            continue
        inner = None
        for e in envs:
            if e[1] <= m.start() < e[2] and (inner is None or e[1] > inner[1]):
                inner = e
        if inner is None:
            break
        base = inner[0].rstrip("*")
        if base in MATH_ENVS:
            return f"Equation~(\\ref{{{label}}})"
        word = KIND_WORDS.get(base) or (extra_words or {}).get(base) or base.capitalize()
        return f"{word}~\\ref{{{label}}}"
    return None


def statement_of(label, parsed):
    """Text of the innermost statement/math environment containing \\label{label}, whitespace
    normalised, comments and labels removed. parsed: [(text, envs)]. Returns (text|None, problem|None)."""
    pat = re.compile(r"\\label\{" + re.escape(label) + r"\}")
    for text, envs in parsed:
        m = pat.search(text)
        if not m:
            continue
        best = None
        for e in envs:
            if e[1] <= m.start() < e[2] and (best is None or e[1] > best[1]):
                best = e
        if best is None:
            return None, f"label {label} is not inside a theorem-like or display-math environment"
        body = re.sub(r"\\label\{[^}]*\}", "", text[best[1]:best[2]])
        return f"{best[0]}: " + " ".join(body.split()), None
    return None, f"label {label} not found in the paper source"


def statement_source(label, parsed):
    """(environment name, optional argument, body) of the statement/display-math environment containing
    \\label{label}, with comments (already stripped) and \\label commands removed, line breaks kept so the
    body can be typeset in the paper's own macros. None if the label is not found or not in an environment."""
    pat = re.compile(r"\\label\{" + re.escape(label) + r"\}")
    for text, envs in parsed:
        m = pat.search(text)
        if not m:
            continue
        best = None
        for e in envs:
            if e[1] <= m.start() < e[2] and (best is None or e[1] > best[1]):
                best = e
        if best is None:
            return None
        body = re.sub(r"\\label\{[^}]*\}", "", text[best[1]:best[2]]).strip()
        opt = ""
        om = re.match(r"\[((?:[^\[\]{}]|\{[^{}]*\})*)\]", body)
        if om and best[0].rstrip("*") not in MATH_ENVS:
            opt, body = om.group(1), body[om.end():].strip()
        return best[0].rstrip("*"), opt, body
    return None


def retag_math(text):
    """Make the display-math environments of `text` unnumbered and show each \\label as an explicit \\tag, so that the
    paper's own equation numbers appear (via \\ref, resolved from the paper's .aux) without the packet's counters."""
    def starred(m):
        return f"\\{m.group(1)}{{{m.group(2)}*}}" if not m.group(2).endswith("*") and m.group(2) in MATH_ENVS else m.group(0)
    text = re.sub(r"\\(begin|end)\{([A-Za-z]+\*?)\}", starred, text)
    inside = []

    def tag_labels(m):
        return re.sub(r"\\label\{([^}]*)\}", r"\\tag{\\ref{\1}}", m.group(0))
    text = re.sub(r"\\begin\{(" + "|".join(MATH_ENVS) + r")\*\}.*?\\end\{\1\*\}", tag_labels, text, flags=re.S)
    return re.sub(r"\\label\{[^}]*\}", "", text)  # labels outside display math (sections, ...) are dropped


def drop_envs(text, names):
    """`text` without the environments named in `names` (reading aids such as explainer boxes that are not part of the
    paper's mathematics), and a function mapping a position of the old text to the new one."""
    spans = sorted((m.start(), m.end()) for nm in names
                   for m in re.finditer(r"\\begin\{%s\}.*?\\end\{%s\}" % (re.escape(nm), re.escape(nm)), text, re.S))
    pieces, last = [], 0
    for a, b in spans:
        if a >= last:
            pieces.append(text[last:a]); last = b
    pieces.append(text[last:])
    return "".join(pieces), (lambda pos: pos - sum(b - a for a, b in spans if b <= pos))


def statement_context(label, parsed, skip=()):
    """For a label inside a display-math environment: the whole paragraph around it (the sentence that gives the
    equation its meaning and hypotheses), retagged by retag_math. None if `label` is not in a math environment."""
    pat = re.compile(r"\\label\{" + re.escape(label) + r"\}")
    for text, envs in parsed:
        m = pat.search(text)
        if not m:
            continue
        best = None
        for e in envs:
            if e[1] <= m.start() < e[2] and (best is None or e[1] > best[1]):
                best = e
        if best is None or best[0].rstrip("*") not in MATH_ENVS:
            return None
        begin = text.rfind("\\begin{" + best[0] + "}", 0, best[1])
        end = text.find("\\end{" + best[0] + "}", best[2]) + len("\\end{" + best[0] + "}")
        if skip:
            text, remap = drop_envs(text, skip)
            begin, end = remap(begin), remap(end)
        gaps = [g for g in re.finditer(r"\n(?:[ \t]*\n)+", text)]  # a run of blank lines is one boundary
        lefts = [g.end() for g in gaps if g.end() <= begin]
        left = lefts[-2] if len(lefts) >= 2 else 0  # also the paragraph before: it usually defines what the equation uses
        if begin - left > 2500:
            left = lefts[-1] if lefts else 0
        right = min([g.start() for g in gaps if g.start() >= end] or [len(text)])
        return retag_math(text[left:right]).strip()
    return None


# Lean source text in LaTeX: symbols that Lean/Mathlib sources use, typeset in math mode
LEAN_SYMBOLS = {
    "∀": r"\forall", "∃": r"\exists", "→": r"\to", "←": r"\leftarrow", "↔": r"\leftrightarrow", "⟶": r"\longrightarrow",
    "∧": r"\land", "∨": r"\lor", "¬": r"\neg", "≤": r"\le", "≥": r"\ge", "≠": r"\ne", "<": "<", ">": ">",
    "∈": r"\in", "∉": r"\notin", "⊆": r"\subseteq", "⊂": r"\subset", "∪": r"\cup", "∩": r"\cap", "∅": r"\emptyset",
    "∑": r"\sum", "∏": r"\prod", "∫": r"\int", "√": r"\surd", "∞": r"\infty", "×": r"\times", "·": r"\cdot",
    "∘": r"\circ", "⊗": r"\otimes", "⊕": r"\oplus", "†": r"\dagger", "ᵀ": r"^{T}", "‖": r"\|", "∣": r"\mid",
    "⟨": r"\langle", "⟩": r"\rangle", "⌊": r"\lfloor", "⌋": r"\rfloor", "⌈": r"\lceil", "⌉": r"\rceil",
    "ℝ": r"\mathbb{R}", "ℕ": r"\mathbb{N}", "ℂ": r"\mathbb{C}", "ℤ": r"\mathbb{Z}", "ℚ": r"\mathbb{Q}",
    "≈": r"\approx", "≡": r"\equiv", "∼": r"\sim", "↦": r"\mapsto", "⊢": r"\vdash", "⊤": r"\top", "⊥": r"\bot",
    "⁻": r"^{-}", "⁺": r"^{+}", "¹": r"^{1}", "²": r"^{2}", "³": r"^{3}", "⁰": r"^{0}", "ⁿ": r"^{n}", "ᵏ": r"^{k}",
    "₀": r"_{0}", "₁": r"_{1}", "₂": r"_{2}", "₃": r"_{3}", "₄": r"_{4}", "₅": r"_{5}", "₆": r"_{6}", "₇": r"_{7}",
    "₈": r"_{8}", "₉": r"_{9}", "ₙ": r"_{n}", "ₖ": r"_{k}", "ᵢ": r"_{i}", "ⱼ": r"_{j}", "ₐ": r"_{a}", "ₘ": r"_{m}",
    "𝟙": "1", "∂": r"\partial", "∇": r"\nabla", "⋯": r"\cdots", "…": r"\ldots", "‹": "<", "›": ">",
    "∗": "*", "⊓": r"\sqcap", "⊔": r"\sqcup", "∖": r"\setminus", "≃": r"\simeq", "≅": r"\cong", "∠": r"\angle",
    "⇒": r"\Rightarrow", "⇔": r"\Leftrightarrow", "⟹": r"\Longrightarrow", "↑": r"\uparrow", "↓": r"\downarrow",
    "★": r"\star", "∙": r"\bullet", "•": r"\bullet", "“": "``", "”": "''", "‘": "`", "’": "'", "–": "--", "—": "---",
}


def uni_tex(ch):
    """One character of Lean source as TeX for a monospaced block (text-mode safe)."""
    if ch in TEX_SPECIAL:
        return TEX_SPECIAL[ch]
    if ord(ch) < 128:
        return ch
    if ch in LEAN_SYMBOLS:
        return "\\ensuremath{" + LEAN_SYMBOLS[ch] + "}"
    name = unicodedata.name(ch, "")
    if name.startswith("GREEK"):
        word = name.split()[-1].lower()
        word = {"lamda": "lambda", "epsilon": "varepsilon"}.get(word, word)
        return "\\ensuremath{\\" + (word.capitalize() if "CAPITAL" in name else word) + "}"
    if unicodedata.category(ch) == "Mn":
        return ""
    if ord(ch) < 256:
        return ch
    return f"[U+{ord(ch):04X}]"


def lean_to_tex(text):
    """Lean source as a block of typeset monospaced lines (indentation kept, long lines wrap)."""
    out = []
    for line in text.splitlines():
        stripped = line.lstrip(" ")
        indent = len(line) - len(stripped)
        if not stripped:
            out.append("\\vspace{0.6ex}")
            continue
        out.append(f"\\hangindent={indent + 2}\\lttw\\hangafter=1\\hspace*{{{indent}\\lttw}}"
                   + "".join(uni_tex(ch) for ch in stripped) + "\\par")
    return ("{\\ttfamily\\scriptsize\\raggedright\\setlength{\\parindent}{0pt}\\setlength{\\parskip}{0pt}"
            "\\settowidth{\\lttw}{\\texttt{x}}\n" + "\n".join(out) + "}")


# ---------------------------------------------------------------- loading
class Ledger:
    def __init__(self, root, paper=None):
        self.root = Path(root).resolve()
        self.dir = self.root / "ledger"
        cfgfile = self.dir / "ledger.toml"
        if not cfgfile.exists():
            sys.exit(f"{cfgfile} not found")
        self.cfg = tomllib.loads(cfgfile.read_text())
        self.paper = paper
        self.errors, self.warnings = [], []
        self.load_human()
        self.load_lean()
        self.load_proverif()
        self.load_papers()
        self.build()

    def load_human(self):
        self.claims, self.citations, self.assertions, self.attestations, self.keys = {}, {}, {}, [], {}
        self.hypotheses, self.assessments = {}, {}
        for f in sorted(self.dir.glob("*.toml")):
            if f.name == "ledger.toml":
                continue
            t = tomllib.loads(f.read_text())
            self.claims.update(t.get("claim", {}))
            self.citations.update(t.get("citation", {}))
            self.assertions.update(t.get("assertion", {}))
            self.attestations += t.get("attestation", [])
            self.keys.update(t.get("key", {}))
            self.hypotheses.update(t.get("hypothesis", {}))
            self.assessments.update(t.get("assessment", {}))
        for n, c in self.claims.items():
            if c.get("evidence", "E5") not in EVIDENCE:
                self.errors.append(f"claim {n}: unknown evidence type {c['evidence']!r}")
        self.apply_scope()
        for a in self.attestations:
            if bool(a.get("claim")) == bool(a.get("hypothesis")):
                self.errors.append(f"attestation by {a.get('person')}: needs exactly one of `claim` and `hypothesis`")
            if a.get("level") not in LEVELS:
                self.errors.append(f"attestation on {a.get('claim')}: unknown level {a.get('level')!r}")
            elif a["level"] == "yellow" and not a.get("reason"):
                self.errors.append(f"attestation on {a.get('claim')}: yellow needs a reason")
        for n, a in self.assessments.items():
            if a.get("verdict") not in ASSESSMENT_VERDICTS:
                self.errors.append(f"assessment {n}: verdict must be one of {', '.join(ASSESSMENT_VERDICTS)}")
        for k, key in self.keys.items():
            try:
                key["fingerprint"] = fingerprint(key["public"])
            except Exception:
                self.errors.append(f"key {k}: unreadable public key")

    @property
    def lockfile(self):
        return self.dir / ("lock.json" if self.paper is None else f"lock-{self.paper}.json")

    def apply_scope(self):
        """With a paper selected keep its claims (and those without a paper), plus every claim they use."""
        papers = self.cfg.get("paper", {})
        if self.paper is None:
            return
        if papers and self.paper not in papers:
            self.errors.append(f"unknown paper {self.paper!r}; configured: {', '.join(sorted(papers))}")
        keep = {n for n, c in self.claims.items() if c.get("paper") in (None, self.paper)}
        todo = list(keep)
        while todo:
            for u in self.claims[todo.pop()].get("uses", []):
                if u in self.claims and u not in keep:
                    keep.add(u); todo.append(u)
        self.claims = {n: c for n, c in self.claims.items() if n in keep}
        self.attestations = [a for a in self.attestations if a.get("claim") in keep or a.get("hypothesis")]
        self.assertions = {k: v for k, v in self.assertions.items() if v.get("claim") in keep}
        used = {x for c in self.claims.values() for x in c.get("cites", [])}
        used |= {x for h in self.hypotheses.values() for x in h.get("cites", [])}
        self.citations = {k: v for k, v in self.citations.items() if k in used}

    def load_papers(self):
        """Paper-source nodes and the parsed statement environments of each paper."""
        self.paper_nodes, self.parsed, self.unresolved, self.flat = {}, {}, {}, {}
        self.extra_result, self.kind_words = {}, {}
        papers = self.cfg.get("paper", {})
        excluded = [(self.root / d).resolve() for d in self.cfg.get("generated", {}).get("dirs", [])]
        for name, pc in papers.items():
            if self.paper is not None and name != self.paper:
                continue
            main = self.root / pc["main"]
            if not main.is_file():
                self.errors.append(f"paper {name}: {main} not found")
                continue
            search = [(self.root / d).resolve() for d in pc.get("texinputs", [])]
            files, unresolved = tex_sources(main, search, excluded)
            self.unresolved[name] = unresolved
            rel = lambda f: str(f.relative_to(self.root)) if self.root in f.parents else str(f)
            self.paper_nodes[name] = dict(main=pc["main"], files={rel(f): sha_file(f) for f in files},
                                          unresolved=unresolved)
            self.flat[name] = flatten_tex(main, search)
            extra_stmt, extra_result, words = discover_theorem_envs(files)
            self.extra_result[name] = extra_result
            self.kind_words.update(words)
            self.parsed[name] = [(t, find_environments(t, extra_stmt)) for t in
                                 (strip_comments(f.read_text(errors="replace")) for f in files if f.suffix == ".tex")]

    def uncovered(self):
        """Labelled theorem-like results of the selected paper(s) that no claim of the ledger covers."""
        claimed = {lab for c in self.claims.values() for lab in (c.get("labels") or ([c["label"]] if c.get("label") else []))}
        claimed |= {h["label"] for h in self.hypotheses.values() if h.get("label")}
        out = []
        for name, parsed in self.parsed.items():
            if self.paper is None or name == self.paper:
                out += [lab for text, envs in parsed for lab in result_labels(text, envs, self.extra_result.get(name, set()))
                        if lab not in claimed]
        return sorted(set(out))

    def hypothesis_statement(self, name, meta):
        """(text, source) of a hypothesis: from the paper by its label if given, else the hand-written text."""
        lab = meta.get("label")
        sources = self.parsed.get(meta.get("paper")) if meta.get("paper") in self.parsed else \
            [x for v in self.parsed.values() for x in v]
        if lab and sources:
            t, problem = statement_of(lab, sources)
            if problem:
                self.errors.append(f"hypothesis {name}: {problem}")
                return "", "tex"
            return f"[{lab}] {t}", "tex"
        return meta.get("text", ""), "manual"

    def label_position(self, c):
        """(file index, offset) of the claim's first label in its paper, for ordering; None if absent."""
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        for lab in labels:
            m = re.search(r"\\label\{" + re.escape(lab) + r"\}", self.flat.get(c.get("paper"), ""))
            if m:
                return (0, m.start())
        return None

    def attestation_summary(self, n):
        """'green'|'yellow'|'conjecture' (strongest current), 'stale' (only stale ones) or 'none'."""
        st = self.attestation_state(n)
        cur = [lvl for _, lvl, _, ok in st if ok]
        for lvl in LEVELS:
            if lvl in cur:
                return lvl
        return "stale" if st else "none"

    def statement(self, n, c):
        """(text, source): the claim's statement from the paper's LaTeX if it has labels, else its `text`."""
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        sources = self.parsed.get(c.get("paper")) if c.get("paper") in self.parsed else \
            [x for v in self.parsed.values() for x in v]
        if not labels or not sources:
            return c.get("text", ""), "manual"
        parts = []
        for lab in labels:
            t, problem = statement_of(lab, sources)
            if problem:
                self.errors.append(f"claim {n}: {problem}")
            else:
                parts.append(f"[{lab}] {t}")
        return "\n".join(parts), "tex"

    def env_files(self):
        """Files of the environment node: paths or globs (relative to the project root), sorted."""
        excluded = [(self.root / d).resolve() for d in self.cfg.get("generated", {}).get("dirs", [])]
        out = set()
        for pat in self.cfg.get("environment", {}).get("files", []):
            for f in self.root.glob(pat):
                r = f.resolve()
                if f.is_file() and not any(x == r or x in r.parents for x in excluded):  # generated files depend on the root
                    out.add(str(f.relative_to(self.root)))
        return sorted(out)

    def env_hash(self):
        return H("env-files", {f: sha_file(self.root / f) for f in self.env_files()})

    def load_lean(self):
        self.decls, self.toolchain = {}, ""
        lc = self.cfg.get("lean")
        if not lc:
            return
        p = self.dir / lc.get("dump", "lean.json")
        if p.exists():
            d = json.loads(p.read_text())
            self.decls, self.toolchain = d["decls"], d.get("toolchain", "")
            if d.get("env_hash") and d["env_hash"] != self.env_hash():
                self.errors.append(f"{p.name} is older than the sources it was extracted from "
                                   "(environment files changed): run `ledger.py extract`")
        elif any(c.get("lean") for c in self.claims.values()):
            self.errors.append(f"{p} missing: run `ledger.py extract`")

    def load_proverif(self):
        """ProVerif dump: {"files": {path: {sha256, queries: {query text: result}}}}."""
        self.pv_files = {}
        pc = self.cfg.get("proverif")
        if not pc:
            return
        p = self.dir / pc.get("dump", "proverif.json")
        if p.exists():
            self.pv_files = json.loads(p.read_text()).get("files", {})
        elif any(c.get("proverif") for c in self.claims.values()):
            self.errors.append(f"{p} missing: run `ledger.py extract`")

    def expand_lean(self, names):
        out = []
        for x in names:
            if x.endswith("*"):
                out += sorted(n for n, d in self.decls.items() if n.startswith(x[:-1]) and d["kind"] == "theorem")
            else:
                out.append(x)
        return out

    # -------------------------------------------------------- graph
    def build(self):
        payload, deps = {}, {}  # full graph
        env_files = {f: sha_file(self.root / f) for f in self.env_files()}
        env = "env:" + self.cfg.get("project", {}).get("name", "project")
        payload[env] = dict(kind="environment", provenance="computed",
                            content=dict(toolchain=self.toolchain, files=env_files))
        deps[env] = []
        self.spec_payload, self.spec_deps = {}, {}
        for n, d in self.decls.items():
            i = "lean:" + n
            if d["kind"] == "theorem" and not d.get("proof_term") and not d.get("proof"):
                self.errors.append(f"dump: theorem {n} has no proof term (extractor bug?)")
            payload[i] = dict(kind="lean-decl", provenance="computed", content=dict(
                {k: v for k, v in d.items() if k not in ("stmt_deps", "proof_deps", "line", "module")}, name=n))
            sd = sorted({"lean:" + x for x in d.get("stmt_deps", []) if x in self.decls})
            pd = sorted({"lean:" + x for x in d.get("proof_deps", []) if x in self.decls})
            deps[i] = sorted(set(sd) | set(pd) | {env})
            self.spec_payload[i] = {k: d.get(k, "") for k in ("kind", "type", "type_term", "value", "value_term")} | dict(name=n)
            self.spec_deps[i] = sd
        for n, c in self.citations.items():
            i = "cite:" + n
            payload[i] = dict(kind="citation", provenance="asserted",
                              content=dict(key=c.get("key", n), statement=c.get("statement", ""), source=c.get("source", "")))
            deps[i] = []
        for n, a in self.assertions.items():
            i = "assert:" + n
            payload[i] = dict(kind="assertion", provenance="asserted", content=dict(claim=a["claim"], text=a["text"]))
            deps[i] = []
        self.files = {}
        for n, c in self.claims.items():
            for f in c.get("files", []):
                i = "file:" + f
                if i in payload:
                    continue
                if not (self.root / f).exists():
                    self.errors.append(f"claim {n}: file {f} not found")
                    continue
                payload[i] = dict(kind="file", provenance="computed", content=dict(path=f, sha256=sha_file(self.root / f)))
                deps[i] = []
        for n, c in self.claims.items():
            for ref in c.get("proverif", []):
                if "#" not in ref:
                    self.errors.append(f"claim {n}: proverif reference {ref!r} must be 'file#query'")
                    continue
                i = "pv:" + ref
                if i in payload:
                    continue
                f, q = ref.split("#", 1)
                fd = self.pv_files.get(f)
                if fd is None:
                    self.errors.append(f"claim {n}: proverif file {f} not in dump")
                    continue
                if q not in fd.get("queries", {}):
                    self.errors.append(f"claim {n}: proverif query {q!r} not in dump for {f}")
                    continue
                payload[i] = dict(kind="proverif-query", provenance="computed",
                                  content=dict(file=f, sha256=fd["sha256"], query=q, result=fd["queries"][q]))
                deps[i] = []
        for k, key in self.keys.items():
            payload["key:" + k] = dict(kind="key", provenance="asserted", content={
                x: key.get(x, "") for x in ("person", "public", "source", "url", "fetched", "revoked")}
                | dict(vouched_by=sorted(key.get("vouched_by", []))))
            deps["key:" + k] = []
        for name, pn in self.paper_nodes.items():
            authors = self.cfg.get("paper", {}).get(name, {}).get("authors", [])
            payload["paper:" + name] = dict(kind="paper-source", provenance="computed", content=dict(pn, authors=sorted(authors)))
            deps["paper:" + name] = ["key:" + a for a in authors if a in self.keys]
            for a in authors:
                if a not in self.keys:
                    self.errors.append(f"paper {name}: author key {a!r} not in keys")
        self.stmt = {}
        for n, c in self.claims.items():
            c["lean"] = self.expand_lean(c.get("lean", []))
            self.stmt[n] = self.statement(n, c)
        # hypotheses the in-scope results are proved given (assumption constants found in their statements)
        self.scope_hyps = sorted({a for c in self.claims.values() for x in c["lean"] if x in self.decls
                                  for a in self.decls[x].get("assumptions", [])})
        self.hstmt = {}
        for h in self.scope_hyps:
            meta = self.hypotheses.get(h, {})
            self.hstmt[h] = self.hypothesis_statement(h, meta)
            payload["hyp:" + h] = dict(kind="hypothesis", provenance="asserted", content=dict(
                name=h, label=meta.get("label", ""), text=self.hstmt[h][0], source=self.hstmt[h][1],
                cites=sorted(meta.get("cites", [])), note=meta.get("note", "")))
            deps["hyp:" + h] = sorted(["cite:" + x for x in meta.get("cites", []) if x in self.citations]
                                      + (["lean:" + h] if h in self.decls else []))
            for x in meta.get("cites", []):
                if x not in self.citations:
                    self.errors.append(f"hypothesis {h}: unknown citation {x}")
        for n, c in self.claims.items():
            i = "claim:" + n
            d = []
            for x in c.get("lean", []):
                if x in self.decls:
                    d.append("lean:" + x)
                else:
                    self.errors.append(f"claim {n}: Lean declaration {x} not in dump")
            d += ["file:" + f for f in c.get("files", []) if "file:" + f in payload]
            d += ["pv:" + r for r in c.get("proverif", []) if "pv:" + r in payload]
            for x in c.get("cites", []):
                if x in self.citations:
                    d.append("cite:" + x)
                else:
                    self.errors.append(f"claim {n}: unknown citation {x}")
            d += ["assert:" + a for a, v in self.assertions.items() if v["claim"] == n]
            rv = self.cfg.get("review", {})
            if rv.get("readings"):  # a model's back-translation of the Lean statement: an aid, never part of the spec hash
                rp = self.root / rv["readings"].format(claim=n)
                if rp.is_file():
                    rid = "reading:" + str(rp.relative_to(self.root))
                    payload[rid] = dict(kind="reading", provenance="generated", content=dict(
                        path=str(rp.relative_to(self.root)), sha256=sha_file(rp), produced_by=rv.get("readings_by", "")))
                    deps[rid] = []
                    d.append(rid)
            if n in self.assessments:  # a model's comparison of paper text, Lean statement and back-translation
                a = self.assessments[n]
                payload["assess:" + n] = dict(kind="assessment", provenance="generated", content=dict(
                    claim=n, model=a.get("model", ""), date=a.get("date", ""), verdict=a.get("verdict", ""),
                    notes=a.get("notes", "")))
                deps["assess:" + n] = []
                d.append("assess:" + n)
            for u in c.get("uses", []):
                if u in self.claims:
                    d.append("claim:" + u)
                else:
                    self.errors.append(f"claim {n}: unknown claim {u} in uses")
            payload[i] = dict(kind="claim", provenance="asserted", content=dict(
                text=self.stmt[n][0], source=self.stmt[n][1], label=c.get("label", ""), evidence=c.get("evidence", "E5")))
            deps[i] = sorted(set(d))
        self.attest_ids = []
        for k, a in enumerate(self.attestations):
            i = f"attest:{k}"
            if a.get("hypothesis"):
                if a["hypothesis"] not in self.scope_hyps:
                    continue  # a hypothesis no result of this scope depends on
                target = "hyp:" + a["hypothesis"]
            else:
                target = "claim:" + a.get("claim", "")
                if target not in payload:
                    self.errors.append(f"attestation {k}: unknown claim {a.get('claim')}")
                    continue
            a["_sig"] = self.check_signature(k, a)
            payload[i] = dict(kind="attestation", provenance="asserted", content={
                x: a.get(x, "") for x in ("claim", "hypothesis", "person", "date", "level", "reason", "bound", "key", "sig")}
                | dict(checklist=a.get("checklist", [])))
            deps[i] = [target] + (["key:" + a["key"]] if a.get("key") in self.keys else [])
            self.attest_ids.append(i)
        self.full = merkle(payload, deps, "node")
        seen, todo = set(), [i for i, q in payload.items() if q["kind"] in ROOT_KINDS]
        while todo:  # keep only what the roots rest on (matters when a paper is selected)
            i = todo.pop()
            if i not in seen:
                seen.add(i); todo += deps.get(i, [])
        payload = {i: q for i, q in payload.items() if i in seen}
        self.full = {i: h for i, h in self.full.items() if i in seen}
        self.payload, self.deps, self.env = payload, deps, env
        # spec hashes of declarations, then of claims
        self.spec = merkle(self.spec_payload, self.spec_deps, "spec")
        cp, cd = {}, {}
        for n, c in self.claims.items():
            cp[n] = dict(text=self.stmt[n][0],
                         lean=[[x, self.spec.get("lean:" + x, "")] for x in sorted(c.get("lean", []))],
                         others=[[i, self.full[i]] for i in sorted(deps["claim:" + n])
                                 if not i.startswith(("lean:", "claim:", "reading:", "assess:"))])
            cd[n] = [u for u in c.get("uses", []) if u in self.claims]
        self.cspec = merkle(cp, cd, "claim-spec")
        self.hspec = {h: H("hyp-spec", dict(text=self.hstmt[h][0], lean=self.spec.get("lean:" + h, ""),
                                           cites=[[x, self.full["cite:" + x]] for x in sorted(self.hypotheses.get(h, {}).get("cites", []))
                                                  if "cite:" + x in self.full]))
                      for h in self.scope_hyps}
        self.root_hash = H("root", [[i, self.full[i]] for i in sorted(payload)
                                    if payload[i]["kind"] in ROOT_KINDS])
        self.register = self.compute_register()

    def check_signature(self, k, a):
        """'unsigned' | 'signed' | 'invalid' | 'unknown-key' | 'revoked' | 'unchecked' for attestation k."""
        if not a.get("sig"):
            return "unsigned"
        key = self.keys.get(a.get("key", ""))
        if key is None:
            self.warnings.append(f"attestation {k} on {a.get('claim')}: signed with unknown key {a.get('key')!r}; treated as unsigned")
            return "unknown-key"
        if key.get("revoked") and a.get("date", "") >= key["revoked"]:
            return "revoked"
        ok = ssh_verify(key["public"], a["key"], a["sig"], attestation_message(self.cfg.get("project", {}).get("name", "project"), a))
        if ok is False:
            self.warnings.append(f"attestation {k} on {a.get('claim')} by {a.get('person')}: SIGNATURE INVALID; it is ignored")
        return "unchecked" if ok is None else ("signed" if ok else "invalid")

    def compute_register(self):
        own = {}
        for n, c in self.claims.items():
            r = set()
            for x in c.get("lean", []):
                d = self.decls.get(x)
                if not d:
                    continue
                r |= {"axiom:" + a for a in d.get("axioms", []) if a not in STANDARD_AXIOMS and a != "sorryAx"}
                if d.get("sorry") or "sorryAx" in d.get("axioms", []):
                    r.add("sorry:" + x)
                r |= {"hyp:" + a for a in d.get("assumptions", [])}
            r |= {"hyp:cited:" + x for x in c.get("cites", [])}
            r |= {"model:" + ref.split("#", 1)[0] for ref in c.get("proverif", [])}
            r |= {"assertion:" + a for a, v in self.assertions.items() if v["claim"] == n}
            if not c.get("lean") and not c.get("files") and not c.get("proverif"):
                r.add("evidence:none")
            own[n] = r
        reg = {n: set(r) for n, r in own.items()}
        changed = True
        while changed:  # least fixed point; terminates since sets only grow
            changed = False
            for n, c in self.claims.items():
                for u in c.get("uses", []):
                    if u in reg and not reg[u] <= reg[n]:
                        reg[n] |= reg[u]; changed = True
        return {n: sorted(r) for n, r in reg.items()}

    # -------------------------------------------------------- derived views
    def lean_status(self, n):
        c = self.claims[n]
        if not c.get("lean"):
            return "-"
        ds = [self.decls.get(x) for x in c["lean"]]
        if any(d is None for d in ds):
            return "missing"
        if any(d.get("sorry") for d in ds):
            return "sorry"
        if any(set(d.get("axioms", [])) - STANDARD_AXIOMS for d in ds):
            return "axioms"
        if any(d.get("assumptions") for d in ds):
            return "assumes"
        return "ok"

    def proverif_status(self, n):
        """'ok' (every query true), 'false' (an attack was found), 'unproved' ('cannot be proved'),
        'missing' (dump does not cover a referenced query) or '-' (no proverif evidence)."""
        refs = self.claims[n].get("proverif", [])
        if not refs:
            return "-"
        results = []
        for ref in refs:
            f, _, q = ref.partition("#")
            fd = self.pv_files.get(f)
            results.append(fd["queries"][q] if fd and q in fd.get("queries", {}) else None)
        if any(r is None for r in results):
            return "missing"
        if any(r == "false" for r in results):
            return "false"
        if any(r != "true" for r in results):
            return "unproved"
        return "ok"

    def hypothesis_state(self, h):
        """Latest attestation per person on hypothesis h -> [(person, level, date, current?)]."""
        latest = {}
        for a in self.attestations:
            if a.get("hypothesis") == h and a.get("_sig") not in ("invalid", "revoked"):
                latest[a.get("person", "?")] = a
        cur = self.hspec.get(h)
        return [(p, a.get("level"), a.get("date", ""), a.get("bound") == cur) for p, a in sorted(latest.items())]

    def known_theorem(self, h):
        """True if someone has a current green attestation that hypothesis h is a known theorem."""
        return any(lvl == "green" and cur for _, lvl, _, cur in self.hypothesis_state(h))

    def claim_hypotheses(self, n):
        return sorted({e[4:] for e in self.register.get(n, []) if e.startswith("hyp:") and not e.startswith("hyp:cited:")})

    def attestation_state(self, n):
        """Latest attestation per person on claim n -> list of (person, level, date, current?)."""
        latest = {}
        for a in self.attestations:
            if a.get("claim") == n and a.get("_sig") not in ("invalid", "revoked"):
                latest[a.get("person", "?")] = a
        cur = self.cspec.get(n)
        return [(p, a.get("level"), a.get("date", ""), a.get("bound") == cur) for p, a in sorted(latest.items())]

    def signature_of(self, n, person):
        """Signature state of the latest counted attestation by `person` on claim n."""
        latest = None
        for a in self.attestations:
            if a.get("claim") == n and a.get("person", "?") == person and a.get("_sig") not in ("invalid", "revoked"):
                latest = a
        return latest.get("_sig", "unsigned") if latest else "unsigned"

    def lock(self):
        return dict(format=0, root=self.root_hash, toolchain=self.toolchain,
                    nodes={i: dict(kind=p["kind"], full=self.full[i]) for i, p in sorted(self.payload.items())},
                    claims={n: dict(spec=self.cspec[n], register=self.register[n]) for n in sorted(self.claims)},
                    hypotheses={h: dict(spec=self.hspec[h]) for h in self.scope_hyps})


# ---------------------------------------------------------------- commands
def cmd_status(L, args):
    word = {"green": "GREEN", "yellow": "YELLOW", "conjecture": "CONJECTURE"}
    rows = [("claim", "evid", "stmt", "lean", "proverif", "attestation", "register")]
    stale = 0
    for n in sorted(L.claims):
        att = []
        for p, lvl, date, cur in L.attestation_state(n):
            att.append(f"{word.get(lvl, lvl)} {p} {'current' if cur else 'STALE'}")
            stale += not cur
        ls = L.lean_status(n)
        hs = L.claim_hypotheses(n)
        if ls == "assumes" and hs:
            k = sum(L.known_theorem(h) for h in hs)
            ls += f" ({k}/{len(hs)} known thm.)" if k else ""
        rows.append((n, L.claims[n].get("evidence", "E5"), L.stmt[n][1], ls, L.proverif_status(n),
                     "; ".join(att) or "none", str(len(L.register[n]))))
    w = [max(len(r[i]) for r in rows) for i in range(7)]
    for r in rows:
        print("  ".join(c.ljust(w[i]) for i, c in enumerate(r)).rstrip())
    if L.scope_hyps:
        print("\nhypotheses (results are proved given these):")
        for h in L.scope_hyps:
            st = L.hypothesis_state(h)
            att = "; ".join(f"{word.get(lvl, lvl)} {p} {'current' if cur else 'STALE'}" for p, lvl, _, cur in st) or "not attested"
            meta = L.hypotheses.get(h, {})
            print(f"  {h}  [{meta.get('label') or 'no label'}; cites {', '.join(meta.get('cites', [])) or 'nothing'}]  {att}")
            stale += any(not cur for *_, cur in st)
    print(f"\nroot {L.root_hash}" + (f"  (paper {L.paper})" if L.paper else ""))
    if L.paper and L.cfg.get("generated", {}).get("dirs"):
        rf = L.root / L.cfg["generated"]["dirs"][0] / f"ledger-{L.paper}-root.tex"
        if rf.exists():
            m = re.search(r"\\def\\LedgerRoot\{([0-9a-f]+)\}", rf.read_text())
            if not m or m.group(1) != L.root_hash:
                print(f"note: {rf.name} shows an older root: run `ledger.py -P {L.paper} tex` before building the paper",
                      file=sys.stderr)
    unc = L.uncovered()
    if unc:
        print(f"warning: {len(unc)} labelled results are not in the ledger: {', '.join(unc[:12])}" + (" ..." if len(unc) > 12 else ""),
              file=sys.stderr)
    for name, u in L.unresolved.items():
        if u:
            print(f"warning: paper {name}: could not resolve {', '.join(u)}", file=sys.stderr)
    for w in L.warnings:
        print("warning:", w, file=sys.stderr)
    for e in L.errors:
        print("error:", e, file=sys.stderr)
    return 1 if L.errors or (args.strict and stale) else 0


def cmd_why(L, args):
    n = args.claim
    if n not in L.claims:
        sys.exit(f"unknown claim {n}")
    c = L.claims[n]
    print(f"{n} [{L.stmt[n][1]}]: {L.stmt[n][0]}\n  evidence {c.get('evidence', 'E5')}, lean {L.lean_status(n)}, "
         f"proverif {L.proverif_status(n)}, spec {L.cspec[n][:12]}")
    print("  rests on:")
    seen, todo = set(), list(L.deps["claim:" + n])
    while todo:
        i = todo.pop()
        if i in seen or i == L.env:
            continue
        seen.add(i)
        todo += L.deps.get(i, [])
    for i in sorted(seen):
        print(f"    {L.payload[i]['provenance']:9} {i}")
    print("  register:", ", ".join(L.register[n]) or "(empty)")
    for p, lvl, date, cur in L.attestation_state(n):
        print(f"  attested {lvl} by {p} on {date}: {'current' if cur else 'STALE (statement changed since)'}")
    return 0


TEX_SPECIAL = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_",
               "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}


def tex_esc(x):
    return "".join(TEX_SPECIAL.get(ch, ch) for ch in str(x))


def cmd_tex(L, args):
    """Write the generated files the paper's \\usepackage{ledgercheck} reads."""
    if not L.paper:
        sys.exit("tex needs a paper: ledger.py -P PAPER tex")
    gen = L.cfg.get("generated", {}).get("dirs", [])
    if not gen:
        sys.exit("ledger.toml: [generated] dirs must name the directory for generated files")
    if L.errors:
        for e in L.errors:
            print("error:", e, file=sys.stderr)
        return 1
    out = L.root / gen[0]
    out.mkdir(parents=True, exist_ok=True)
    pc = L.cfg.get("paper", {}).get(L.paper, {})
    src = L.full.get("paper:" + L.paper, "")[:12]
    tool = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:12]
    r = L.root_hash
    lines = [f"% generated by ledger.py -P {L.paper} tex; do not edit. Excluded from the hashed source.",
             f"\\def\\LedgerPaper{{{L.paper}}}", f"\\def\\LedgerRoot{{{r}}}", f"\\def\\LedgerRootShort{{{r[:12]}}}"]
    lines += [f"\\def\\LedgerRoot{c}{{{r[16 * k:16 * k + 16]}}}" for k, c in enumerate("ABCD")]
    lines += [f"\\def\\LedgerSource{{{src}}}", f"\\def\\LedgerTool{{{tool}}}",
              f"\\def\\LedgerFormat{{0}}", f"\\def\\LedgerDate{{{datetime.date.today().isoformat()}}}",
              "\\def\\LedgerSupplement{%s}" % tex_esc(pc.get("supplement", "the supplementary repository of this paper")),
              "\\def\\LedgerVerify{%s}" % tex_esc(pc.get("verify", f"python3 ledger.py -P {L.paper} verify"))]
    (out / f"ledger-{L.paper}-root.tex").write_text("\n".join(lines) + "\n")

    # one row per label (readers look up "Theorem X"); a claim without labels gets one row under its name
    def label_pos(c, lab):
        m = re.search(r"\\label\{" + re.escape(lab) + r"\}", L.flat.get(c.get("paper"), ""))
        return (0, m.start(), 0) if m else (1, 0, 0)
    entries = []
    for n, c in L.claims.items():
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        entries += [(label_pos(c, lab), lab, n) for lab in labels] or [((2, 0, 0), n, n)]
    entries.sort()
    names = sorted(L.claims)
    cnt = dict(green=0, yellow=0, conjecture=0, stale=0, none=0)
    assumes = sorry = 0
    for n in names:
        cnt[L.attestation_summary(n)] += 1
        ls = L.lean_status(n)
        assumes += ls == "assumes"; sorry += ls == "sorry"
    def reference(c, lab):
        parsed = L.parsed.get(c.get("paper")) or [x for v in L.parsed.values() for x in v]
        return reference_tex(lab, parsed, L.kind_words)
    def hyp_pos(h):
        lab = L.hypotheses.get(h, {}).get("label")
        m = re.search(r"\\label\{" + re.escape(lab) + r"\}", next(iter(L.flat.values()), "")) if lab else None
        return (0, m.start(), h) if m else (1, 0, h)
    hkey = {h: f"H{i + 1}" for i, h in enumerate(sorted(L.scope_hyps, key=hyp_pos))}
    rows = []
    seen = {}
    for _, lab, n in entries:
        seen[lab] = seen.get(lab, 0) + 1
    for _, lab, n in entries:
        c = L.claims[n]
        ls = L.lean_status(n)
        st = L.attestation_state(n)
        cell = f"\\LedgerLeanCell{{{ls if ls != '-' else 'none'}}}"
        if ls == "assumes" and L.claim_hypotheses(n):
            cell = "\\LedgerLeanGiven{" + ", ".join(hkey[h] for h in sorted(L.claim_hypotheses(n), key=lambda h: hkey[h])) + "}"
        pvs = L.proverif_status(n)
        pvcell = f"\\LedgerProverifCell{{{pvs if pvs != '-' else 'none'}}}"
        att = ("\\LedgerAtts{" + "\\\\[2pt]".join(
            f"\\LedgerAtt{{{lvl}}}{{{tex_esc(p)}}}{{{tex_esc(date)}}}{{{'current' if cur else 'stale'}}}{{{L.signature_of(n, p)}}}"
            for p, lvl, date, cur in st) + "}") if st else "\\LedgerNoAtt"
        ref = reference(c, lab)
        res = (f"{ref} {{\\scriptsize\\texttt{{{tex_esc(lab)}}}}}" if ref else f"\\texttt{{{tex_esc(lab)}}}") \
            + (f" {{\\scriptsize({tex_esc(n)})}}" if seen[lab] > 1 and lab != n else "")
        rows.append(f"\\LedgerRow{{{res}}}{{{c.get('evidence', 'E5')}}}{{{L.stmt[n][1]}}}"
                    f"{{{cell}}}{{{pvcell}}}{{{len(L.register[n])}}}{{{att}}}")
    counted = [(n, p) for n in names for p, *_ in L.attestation_state(n)]
    nsigned = sum(L.signature_of(n, p) == "signed" for n, p in counted)
    keyrows = []
    for i, q in sorted(L.payload.items()):
        if q["kind"] == "key":
            kc = q["content"]
            keyrows.append(f"\\LedgerKeyRow{{{tex_esc(kc['person'])}}}{{{tex_esc(fingerprint(kc['public']))}}}"
                           f"{{{tex_esc(kc.get('source') or 'paper')}}}{{{'revoked ' + tex_esc(kc['revoked']) if kc.get('revoked') else ''}}}%")
    hrows = []
    for h in sorted(L.scope_hyps, key=lambda h: hkey[h]):
        meta = L.hypotheses.get(h, {})
        lab = meta.get("label")
        ref = (reference_tex(lab, [x for v in L.parsed.values() for x in v], L.kind_words) if lab else None) or "---"
        hst = L.hypothesis_state(h)
        att = ("\\LedgerAtts{" + "\\\\[2pt]".join(
            f"\\LedgerAtt{{{lvl}}}{{{tex_esc(p)}}}{{{tex_esc(date)}}}{{{'current' if cur else 'stale'}}}{{unsigned}}"
            for p, lvl, date, cur in hst) + "}") if hst else "\\LedgerNoAtt"
        hrows.append(f"\\LedgerHypRow{{{hkey[h]}}}{{{ref}}}{{\\texttt{{{tex_esc(h)}}}}}{{{tex_esc(', '.join(meta.get('cites', [])) or '---')}}}{{{att}}}%")
    nknown = sum(L.known_theorem(h) for h in L.scope_hyps)
    allparsed = [x for v in L.parsed.values() for x in v]
    flat = next(iter(L.flat.values()), "")

    def unc_pos(lab):
        m = re.search(r"\\label\{" + re.escape(lab) + r"\}", flat)
        return m.start() if m else 1 << 60
    uncovered_refs = [f"{reference_tex(lab, allparsed, L.kind_words) or ''} {{\\scriptsize\\texttt{{{tex_esc(lab)}}}}}".strip()
                      for lab in sorted(L.uncovered(), key=unc_pos)]
    cl = [f"% generated by ledger.py -P {L.paper} tex; do not edit. Excluded from the hashed source.",
          f"\\def\\LedgerNClaims{{{len(names)}}}", f"\\def\\LedgerNAtt{{{len(counted)}}}",
          f"\\def\\LedgerNHyp{{{len(L.scope_hyps)}}}", f"\\def\\LedgerNHypKnown{{{nknown}}}",
          "\\def\\LedgerHyps{%"] + hrows + ["}",
          f"\\def\\LedgerNSignedAtt{{{nsigned}}}", f"\\def\\LedgerNKeys{{{len(keyrows)}}}",
          f"\\def\\LedgerNUncovered{{{len(L.uncovered())}}}",
          "\\def\\LedgerUncovered{%s}" % ", ".join(uncovered_refs),
          "\\def\\LedgerKeys{%"] + keyrows + ["}"]
    cl += [f"\\def\\LedgerN{k}{{{v}}}" for k, v in (("Green", cnt["green"]), ("Yellow", cnt["yellow"]),
           ("Conj", cnt["conjecture"]), ("Stale", cnt["stale"]), ("None", cnt["none"]), ("Assumes", assumes), ("Sorry", sorry))]
    # plain tabulars of CHUNK rows each: page breaks fall between them (longtable/supertabular fail in
    # the two-column journal class)
    CHUNK = 8
    cl += ["\\def\\LedgerChunks{%"]
    for k in range(0, len(rows), CHUNK):
        cl += ["\\LedgerTable{%"] + [r + "%" for r in rows[k:k + CHUNK]] + ["}%"]
    cl += ["}"]
    (out / f"ledger-{L.paper}-status.tex").write_text("\n".join(cl) + "\n")
    print(f"wrote {out / f'ledger-{L.paper}-root.tex'} and {out / f'ledger-{L.paper}-status.tex'}")
    print(r)
    return 0




# ---------------------------------------------------------------- review packet
ITALIC_ENVS = {"theorem", "lemma", "proposition", "corollary", "claim", "fact", "observation", "conjecture"}
VERDICT_TEXT = {"consistent": "CONSISTENT", "partial": "PARTIAL", "check": "CHECK", "mismatch": "MISMATCH", "unclear": "UNCLEAR"}


def lean_status_words(L, n):
    ls = L.lean_status(n)
    if ls == "ok":
        return "checked, standard axioms only"
    if ls == "assumes":
        return "checked, given " + ", ".join(tex_esc(h) for h in L.claim_hypotheses(n))
    return {"-": "no Lean declaration", "sorry": "CONTAINS SORRY", "axioms": "extra axioms",
            "missing": "declaration missing"}.get(ls, ls)


def review_statement_tex(L, lab, parsed, seen):
    skip = L.cfg.get("review", {}).get("skip_envs", [])
    """The paper's statement for `lab`, typeset in the paper's own macros with the paper's number."""
    src = statement_source(lab, parsed)
    if src is None:
        return f"\\noindent\\textit{{(label {tex_esc(lab)} not found in the source)}}\\par"
    env, opt, body = src
    if env in MATH_ENVS:
        ctx = statement_context(lab, parsed, skip)
        if ctx in seen:
            return ""
        seen.add(ctx)
        return f"\\noindent\\textbf{{Equation~(\\ref{{{lab}}}), with the paragraph before it and its own:}}\\par\\smallskip\\noindent {ctx}\\par"
    body = retag_math(body)
    if (env, body) in seen:
        return ""
    seen.add((env, body))
    word = KIND_WORDS.get(env) or L.kind_words.get(env) or env.capitalize()
    head = f"{word}~\\ref{{{lab}}}" + (f" ({opt})" if opt else "")
    style = "\\itshape " if env in ITALIC_ENVS else ""
    return f"\\noindent\\textbf{{{head}.}}~{{{style}{body}\\par}}"


def review_body(L, only=None, with_lean=True):
    """LaTeX body of the review packet of the selected paper: for each claim the paper's statement, the model's
    back-translation of the Lean statement, a model's short assessment and the Lean text."""
    rv = L.cfg.get("review", {})
    parsed = L.parsed.get(L.paper) or [x for v in L.parsed.values() for x in v]
    root = L.root
    names = [n for n in L.claims if not only or n in only]
    names.sort(key=lambda n: (L.label_position(L.claims[n]) or (1, 0), n))
    out = [r"\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}",
           r"\newlength{\lttw}", r"\onecolumn", r"\setlength{\parindent}{0pt}", r"\setlength{\parskip}{4pt}",
           r"\pagestyle{plain}"]
    out.append(r"{\Large\bfseries Review packet for the claims of the paper ``%s''}\par\medskip" % tex_esc(L.paper))
    out.append(r"Ledger root of the paper (this packet is not part of it): \texttt{%s}.\par" % L.root_hash[:32])
    out.append(r"""\medskip\textbf{How to use.} Each claim has its own page(s): \emph{In the paper} is the statement as typeset in the
paper, with the paper's numbers and the page where it stands (page numbers refer to the plain build of the paper made for this packet). \emph{Back-translation}
is what a model reads out of the Lean statement alone; \emph{Assessment} is a model's short comparison of the three. Both are
generated aids and can share a model's blind spots; neither is an attestation. \emph{Lean statement} is the source the back-translation
was made from. To attest after reading: \texttt{ledger.py -P %s attest CLAIM --person NAME --level yellow --reason spec}.\par
\medskip\textbf{Verdicts.} CONSISTENT: no difference found between paper, back-translation and Lean text. PARTIAL: faithful where it formalises, but this claim covers only part of what the paper states under its label (the rest is in a sibling claim or not formalised; see the notes). CHECK: something specific to look at, see the notes.
MISMATCH: a difference that probably needs a fix in the text or in the formalisation. UNCLEAR: could not be decided.\par
\medskip\textbf{Claims} (page):\par\smallskip""" % tex_esc(L.paper))
    idx = ", ".join(f"\\texttt{{{tex_esc(n)}}}~(\\pageref{{rv:{n}}})" for n in names)
    out.append("{\\small " + idx + "}")
    for n in names:
        c = L.claims[n]
        labels = c.get("labels") or ([c["label"]] if c.get("label") else [])
        where = []
        for lab in labels:
            ref = reference_tex(lab, parsed, L.kind_words)
            where.append(f"{ref or tex_esc(lab)} (p.~\\pageref{{{lab}}})")
        att = L.attestation_state(n)
        atts = "; ".join(f"{lvl.upper()} by {tex_esc(p)}" + ("" if cur else " (stale)") for p, lvl, _, cur in att) or "not yet attested"
        out.append("\\clearpage")
        out.append(f"{{\\Large\\bfseries Claim \\texttt{{{tex_esc(n)}}}}}\\label{{rv:{n}}}\\par\\smallskip")
        out.append(f"{{\\small \\textbf{{In the paper:}} {'; '.join(where) or 'no label (ledger text only)'}.\\quad "
                   f"\\textbf{{Evidence}} {tex_esc(c.get('evidence', 'E5'))}; \\textbf{{Lean}}: {lean_status_words(L, n)}; "
                   f"\\textbf{{attestation}}: {atts}.}}\\par\\medskip")
        out.append("{\\large\\bfseries In the paper}\\par\\smallskip")
        seen = set()
        if labels:
            out += [review_statement_tex(L, lab, parsed, seen) for lab in labels]
        else:
            out.append("\\noindent\\textit{No label in the paper; text recorded in the ledger:} " + tex_esc(L.stmt[n][0]))
        out.append("\\par\\medskip")
        rd = rv.get("readings") and (root / rv["readings"].format(claim=n))
        out.append("{\\large\\bfseries Back-translation of the Lean statement} {\\small(generated by a model from the Lean text alone)}\\par\\smallskip")
        out.append(f"\\input{{readings/{n}}}" if rd and rd.is_file() else "\\noindent\\textit{No back-translation file for this claim.}")
        out.append("\\par\\medskip")
        a = L.assessments.get(n)
        out.append("{\\large\\bfseries Assessment} {\\small(generated by a model; an aid for the reviewer, not an attestation)}\\par\\smallskip")
        if a:
            out.append(f"\\noindent\\textbf{{{VERDICT_TEXT.get(a.get('verdict'), a.get('verdict', '?'))}}} "
                       f"{{\\small({tex_esc(a.get('model', '?'))}, {tex_esc(a.get('date', ''))})}}\\par\n{a.get('notes', '')}")
        else:
            out.append("\\noindent\\textit{No assessment yet.}")
        ex = rv.get("extracts") and (root / rv["extracts"].format(claim=n))
        if with_lean and ex and ex.is_file():
            text = ex.read_text(errors="replace")
            text = re.sub(r"\A\s*/-.*?-/\s*", "", text, count=1, flags=re.S) if text.lstrip().startswith("/-") else text
            text = re.sub(r"(?m)^import .*\n", "", text)
            out.append("\\par\\medskip{\\large\\bfseries Lean statement} {\\small(source extract: definitions, then the statement)}\\par\\smallskip")
            out.append(lean_to_tex(text.strip("\n")))
    if L.scope_hyps:
        out.append("\\clearpage{\\Large\\bfseries Hypotheses}\\par\\smallskip")
        for h in L.scope_hyps:
            meta = L.hypotheses.get(h, {})
            out.append(f"\\noindent\\textbf{{\\texttt{{{tex_esc(h)}}}}}\\quad cites: {tex_esc(', '.join(meta.get('cites', [])) or 'nothing')}.\\par")
            if meta.get("label"):
                out.append(review_statement_tex(L, meta["label"], parsed, set()))
            d = L.decls.get(h, {})
            if with_lean and d.get("value"):
                out.append(lean_to_tex(f"def {h} :=\n  {d['value']}"))
            st = L.hypothesis_state(h)
            out.append("\\noindent\\textit{Attestation as a known theorem:} " +
                       ("; ".join(f"{lvl.upper()} by {tex_esc(p)}" + ("" if cur else " (stale)") for p, lvl, _, cur in st) or "not yet attested") + "\\par\\medskip")
    return "\n".join(out) + "\n"


def cmd_review(L, args):
    """Build the review packet PDF of one paper: statements side by side with the back-translations."""
    if not L.paper:
        sys.exit("review needs a paper: ledger.py -P PAPER review")
    if L.errors:
        for e in L.errors:
            print("error:", e, file=sys.stderr)
        return 1
    pc = L.cfg["paper"][L.paper]
    main = (L.root / pc["main"]).resolve()
    search = [(L.root / d).resolve() for d in pc.get("texinputs", [])]
    outdir = Path(args.out or L.cfg.get("review", {}).get("out", "review"))
    outdir = outdir if outdir.is_absolute() else L.root / outdir
    outdir.mkdir(parents=True, exist_ok=True)
    tmp = Path(tempfile.mkdtemp(prefix="ledger-review-"))
    dirs = [main.parent, *search]
    env = dict(os.environ, TEXINPUTS=os.pathsep.join(f"{d}//" for d in dirs) + os.pathsep,
               BIBINPUTS=os.pathsep.join(str(d) for d in dirs) + os.pathsep,
               BSTINPUTS=os.pathsep.join(str(d) for d in dirs) + os.pathsep)
    try:
        if args.aux:
            aux = Path(args.aux)
        else:  # a plain build of the paper in a scratch directory gives the labels, numbers, pages and citations
            print("building the paper once for its numbers and page references ...", file=sys.stderr)
            # the paper's own ledger appendix (ledgercheck) is not needed for the numbers: switch it off
            no_appendix = "-usepretex=\\AddToHook{begindocument/end}{\\ifcsname ledgercheck@placedtrue\\endcsname\\csname ledgercheck@placedtrue\\endcsname\\fi}"
            r = subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", no_appendix, f"-outdir={tmp / 'paper'}", str(main)],
                               cwd=tmp, env=env, capture_output=True, text=True, errors="replace")
            aux = tmp / "paper" / (main.stem + ".aux")
            if not aux.exists():
                print(r.stdout[-2000:], r.stderr[-2000:])
                sys.exit("the paper did not build; pass --aux FILE to use an existing .aux")
        work = tmp / "work"
        (work / "readings").mkdir(parents=True)
        shutil.copy(aux, work / "review.aux")
        rv = L.cfg.get("review", {})
        for n in L.claims:
            if rv.get("readings"):
                rp = L.root / rv["readings"].format(claim=n)
                if rp.is_file():
                    shutil.copy(rp, work / "readings" / f"{n}.tex")
        only = set(args.claims.split(",")) if args.claims else None
        body = review_body(L, only, with_lean=not args.no_lean)
        (work / "review-body.tex").write_text(body)
        # amsmath/amssymb: the packet uses starred display environments and \\tag, whatever the paper loads
        inject = ("\\AddToHook{begindocument/before}{\\RequirePackage{amsmath,amssymb}}"
                  "\\AddToHook{begindocument/end}{\\ifcsname ledgercheck@placedtrue\\endcsname\\csname ledgercheck@placedtrue\\endcsname\\fi"
                  "\\input{review-body}\\end{document}}\\input{" + main.stem + "}")  # no ledger appendix in the packet (csname: '@' is not a letter here)
        log = ""
        paper_aux = (work / "review.aux").read_text(errors="replace")
        for _ in range(2):  # the second pass settles \pageref
            r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-jobname=review", inject], cwd=work, env=env,
                               capture_output=True, text=True, errors="replace")
            log = (work / "review.log").read_text(errors="replace") if (work / "review.log").exists() else r.stdout
            # a pass overwrites review.aux with only its own labels; keep the paper's and add the packet's page labels
            mine = [l for l in (work / "review.aux").read_text(errors="replace").splitlines() if l.startswith("\\newlabel{rv:")]
            (work / "review.aux").write_text(paper_aux.rstrip("\n") + "\n" + "\n".join(mine) + "\n")
        pdf = work / "review.pdf"
        if not pdf.exists():
            print(log[-3000:])
            sys.exit("the packet did not build")
        nerr = len(re.findall(r"(?m)^!", log))
        target = outdir / f"{L.paper}-review.pdf"
        shutil.copy(pdf, target)
        shutil.copy(work / "review-body.tex", outdir / f"{L.paper}-review-body.tex")
        print(f"{target}" + (f" ({nerr} LaTeX errors)" if nerr else ""))
        if nerr:
            (outdir / f"{L.paper}-review.log").write_text(log)
            print(f"LaTeX reported {nerr} errors; log in {outdir / (L.paper + '-review.log')}", file=sys.stderr)
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def cmd_lock(L, args):
    if L.errors:
        for e in L.errors:
            print("error:", e, file=sys.stderr)
        return 1
    L.lockfile.write_text(json.dumps(L.lock(), indent=1, sort_keys=True) + "\n")
    print(L.root_hash)
    return 0


def cmd_verify(L, args):
    f = L.lockfile
    if not f.exists():
        sys.exit(f"no {f.name}: run `lock` first")
    old, new, bad = json.loads(f.read_text()), L.lock(), list(L.errors)
    for i in sorted(set(old["nodes"]) | set(new["nodes"])):
        a, b = old["nodes"].get(i), new["nodes"].get(i)
        if a is None:
            bad.append(f"new node {i}")
        elif b is None:
            bad.append(f"node removed: {i}")
        elif a["full"] != b["full"]:
            bad.append(f"changed: {i}")
    for n in sorted(set(old["claims"]) & set(new["claims"])):
        if old["claims"][n]["register"] != new["claims"][n]["register"]:
            bad.append(f"register of claim {n} differs")
    if old["root"] != new["root"] and not bad:
        bad.append("root differs")
    for b in bad:
        print(b)
    print("OK" if not bad else "FAILED", "root", new["root"])
    return 1 if bad else 0


def toml_record(table, rec):
    return f"\n{table}\n" + "".join(f"{k} = {json.dumps(v, ensure_ascii=False)}\n" for k, v in rec.items())


def cmd_attest(L, args):
    if bool(args.claim) == bool(args.hypothesis):
        sys.exit("give exactly one of CLAIM and --hypothesis NAME")
    if args.hypothesis:
        if args.hypothesis not in L.scope_hyps:
            sys.exit(f"{args.hypothesis} is not a hypothesis of any result in this scope; known: {', '.join(L.scope_hyps) or 'none'}")
        target, bound = dict(hypothesis=args.hypothesis), L.hspec[args.hypothesis]
    else:
        if args.claim not in L.claims:
            sys.exit(f"unknown claim {args.claim}")
        target, bound = dict(claim=args.claim), L.cspec[args.claim]
    if args.level == "yellow" and not args.reason:
        sys.exit("yellow needs --reason")
    rec = dict(**target, person=args.person, date=datetime.date.today().isoformat(), level=args.level,
               reason=args.reason or "", checklist=[x for x in (args.checklist or "").split(",") if x],
               bound=bound)
    extra = ""
    if args.sign:
        if not args.key:
            sys.exit("--sign needs --key KEYID (a key registered with `addkey`, or --pub for a standalone file)")
        pub = (L.keys.get(args.key) or {}).get("public") or (Path(args.pub).read_text().strip() if args.pub else None)
        if not pub:
            sys.exit(f"key {args.key!r} is not in ledger/keys.toml; register it with `addkey` or pass --pub FILE")
        project = L.cfg.get("project", {}).get("name", "project")
        rec["key"] = args.key
        rec["sig"] = ssh_sign(args.sign, attestation_message(project, rec))
        if ssh_verify(pub, args.key, rec["sig"], attestation_message(project, rec)) is not True:
            sys.exit("the signature does not verify against the registered public key: wrong --sign file for this key?")
        if args.out:  # a standalone file carries the key it was made with
            extra = toml_record(f"[key.{args.key}]", dict(person=args.person, public=pub, source="attestation-file"))
    out = Path(args.out) if args.out else L.dir / "attestations.toml"
    with open(out, "a") as f:
        f.write(extra + toml_record("[[attestation]]", rec))
    print(f"recorded {args.level} by {args.person} on {args.claim or 'hypothesis ' + args.hypothesis}, bound to {rec['bound'][:12]}"
          + (", signed" if "sig" in rec else "") + (f" -> {out}" if args.out else ""))
    return 0


def cmd_addkey(L, args):
    pub = Path(args.pub).read_text().strip() if Path(args.pub).exists() else args.pub.strip()
    rec = dict(person=args.person, public=pub, source=args.source, url=args.url or "",
               fetched=datetime.date.today().isoformat() if args.source == "url" else "",
               vouched_by=[x for x in (args.vouched_by or "").split(",") if x])
    rec = {k: v for k, v in rec.items() if v != "" and v != []}
    with open(L.dir / "keys.toml", "a") as f:
        f.write(toml_record(f"[key.{args.id}]", rec))
    print(f"key {args.id} ({fingerprint(pub)}) for {args.person}, source {args.source}")
    return 0


def cmd_verify_attestation(L, args):
    """Check a standalone attestation file against a lock file (hash only; no ledger sources needed)."""
    t = tomllib.loads(Path(args.file).read_text())
    lock = json.loads(Path(args.lock).read_text())
    project = L.cfg.get("project", {}).get("name", "project")
    bad = 0
    for a in t.get("attestation", []):
        claim = lock["hypotheses"].get(a.get("hypothesis")) if a.get("hypothesis") else lock["claims"].get(a.get("claim"))
        key = (t.get("key", {}) or {}).get(a.get("key", ""), None) or L.keys.get(a.get("key", ""))
        state = []
        state.append("statement matches the lock" if claim and claim["spec"] == a.get("bound")
                     else "STATEMENT DIFFERS from the lock (stale or wrong version)")
        bad += not (claim and claim["spec"] == a.get("bound"))
        if not a.get("sig"):
            state.append("unsigned")
        elif key is None:
            state.append("signed, but the file carries no key"); bad += 1
        else:
            ok = ssh_verify(key["public"], a["key"], a["sig"], attestation_message(project, a))
            state.append(f"signature {'VALID' if ok else 'INVALID' if ok is False else 'unchecked (no ssh-keygen)'}"
                         f" for key {fingerprint(key['public'])} (introduced by this file: check it came from {a.get('person')})")
            bad += ok is False
        print(f"{a.get('level', '?').upper()} by {a.get('person')} on {a.get('claim') or 'hypothesis ' + a.get('hypothesis', '?')} ({a.get('date')}): " + "; ".join(state))
    return 1 if bad else 0


def cmd_extract(L, args):
    lc, pc = L.cfg.get("lean", {}), L.cfg.get("proverif", {})
    if lc.get("extract"):
        names = sorted({x for c in L.claims.values() for x in c.get("lean", [])})
        out = subprocess.run(lc["extract"], shell=True, cwd=L.root, input="\n".join(names), text=True, capture_output=True)
        sys.stderr.write(out.stderr[-3000:])
        if out.returncode:
            return out.returncode
        dump = json.loads(out.stdout)  # must be valid JSON
        L.root = Path(args.dir).resolve()
        dump["env_hash"] = L.env_hash()  # lets later runs notice that the sources moved on
        (L.dir / lc.get("dump", "lean.json")).write_text(json.dumps(dump, separators=(",", ":")))
    elif not pc.get("extract"):
        sys.exit("no [lean] extract command configured")
    if pc.get("extract"):
        files = sorted({r.split("#", 1)[0] for c in L.claims.values() for r in c.get("proverif", [])})
        out = subprocess.run(pc["extract"], shell=True, cwd=L.root, input="\n".join(files), text=True, capture_output=True)
        sys.stderr.write(out.stderr[-3000:])
        if out.returncode:
            return out.returncode
        (L.dir / pc.get("dump", "proverif.json")).write_text(
            json.dumps({"files": json.loads(out.stdout)}, separators=(",", ":")))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-C", dest="dir", default=".")
    ap.add_argument("-P", "--paper", default=None, help="restrict to the claims of one configured paper (own root and lock file)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status"); p.add_argument("--strict", action="store_true")
    sub.add_parser("lock"); sub.add_parser("verify"); sub.add_parser("extract"); sub.add_parser("tex")
    p = sub.add_parser("review", help="build a review packet: paper statements next to back-translations and Lean text")
    p.add_argument("--claims", help="comma-separated claim names (default: all in scope)")
    p.add_argument("--out", help="output directory (default: [review] out, else ./review)")
    p.add_argument("--aux", help="use this .aux of the paper instead of building the paper once")
    p.add_argument("--no-lean", action="store_true", help="leave the Lean source text out")
    p = sub.add_parser("why"); p.add_argument("claim")
    p = sub.add_parser("attest"); p.add_argument("claim", nargs="?"); p.add_argument("--person", required=True)
    p.add_argument("--hypothesis", help="attest a hypothesis (e.g. that it is a known theorem) instead of a claim")
    p.add_argument("--level", required=True, choices=LEVELS); p.add_argument("--reason"); p.add_argument("--checklist")
    p.add_argument("--sign", metavar="PRIVATE_KEY", help="sign with this ssh key file (ssh-keygen -Y sign)")
    p.add_argument("--key", help="id of the signing key in ledger/keys.toml")
    p.add_argument("--pub", help="public key file (standalone attestations by someone who is not in keys.toml)")
    p.add_argument("--out", help="write a standalone attestation file instead of appending to ledger/attestations.toml")
    p = sub.add_parser("addkey"); p.add_argument("id"); p.add_argument("--person", required=True)
    p.add_argument("--pub", required=True, help="public key file or line")
    p.add_argument("--source", choices=("paper", "vouched", "url"), default="paper")
    p.add_argument("--url"); p.add_argument("--vouched-by")
    p = sub.add_parser("verify-attestation"); p.add_argument("file"); p.add_argument("--lock", required=True)
    args = ap.parse_args(argv)
    if args.cmd in ("extract", "verify-attestation", "addkey"):  # no ledger build needed (the dump may not exist yet)
        L = Ledger.__new__(Ledger)
        L.root = Path(args.dir).resolve(); L.dir = L.root / "ledger"
        L.cfg = tomllib.loads((L.dir / "ledger.toml").read_text()); L.errors = []; L.warnings = []; L.paper = args.paper
        L.load_human()
        L.keys = getattr(L, "keys", {})
    else:
        L = Ledger(args.dir, args.paper)
    return globals()["cmd_" + args.cmd.replace("-", "_")](L, args)


if __name__ == "__main__":
    sys.exit(main())
