#!/usr/bin/env python3
"""trust-ledger: a Merkle ledger of the evidence behind a paper's claims.

Single file, Python >= 3.11, standard library only. Normative format: docs/FORMAT.md.
Version 0.2.0 (alpha), ledger format 0.2.0.

  ledger.py [-C DIR] status [--strict]   table of claims: tool status, attestation, register size
  ledger.py [-C DIR] why CLAIM           everything CLAIM rests on, and who attested what
  ledger.py [-C DIR] lock                recompute and write ledger/lock.json (prints the root)
  ledger.py [-C DIR] verify              recompute and compare with lock.json; exit 1 on any difference
  ledger.py [-C DIR] attest CLAIM --person P --level green|yellow|conjecture [--reason R] [--checklist A1,A2]
  ledger.py [-C DIR] extract             run the extractors of the configured adapters (writes their dumps)
  ledger.py [-C DIR] reproduce [STEP...]  re-run command steps in a scratch copy, compare their outputs
  ledger.py [-C DIR] check               run the [check.NAME] commands, record their results (ledger/checks.json)
  ledger.py [-C DIR] commitment PATH --salt-file F   salted commitment to data that stays private
  ledger.py [-C DIR] migrate --old-lock F            rebind attestations after a format change

DIR is the project root; it must contain ledger/ledger.toml.
"""
import argparse, base64, datetime, hashlib, json, os, re, shutil, subprocess, sys, tempfile, tomllib, unicodedata
from pathlib import Path

__version__ = "0.3.0"
FORMAT_VERSION = "0.3.0"          # docs/FORMAT.md; recorded in every lock file
READS_FORMATS = ("0.3.0",)        # older lock files: `ledger.py migrate` (FORMAT.md 6)
LEVELS = ("green", "yellow", "conjecture")
ROOT_KINDS = ("claim", "attestation", "environment", "paper-source", "hypothesis")
ASSESSMENT_VERDICTS = ("consistent", "partial", "check", "mismatch", "unclear")
SIG_NAMESPACE = "trust-ledger-attestation"  # ssh-keygen -Y namespace: a signature cannot be replayed elsewhere
# the default evidence vocabulary (mathematics), strongest first; a project may define its own as [[evidence]]
DEFAULT_EVIDENCE = [dict(id="E1", name="checked proof"), dict(id="E2", name="checked certificate"),
                    dict(id="E3", name="exact computation"), dict(id="E4", name="numerical evidence"),
                    dict(id="E5", name="assertion")]
# adapters (FORMAT.md section 2.6): a claim lists references into an adapter's dump under the adapter's name
CLAIM_FIELDS = {"text", "label", "labels", "paper", "evidence", "files", "provenance", "sources", "uses", "cites", "note",
                "review_name"}
ADAPTER_STATUS = ("ok", "conditional", "open", "failed")  # increasing severity; a claim shows its worst reference
CORE_KINDS = {"file", "source", "step", "paper-source", "claim", "citation", "assertion", "attestation", "key",
              "hypothesis", "reading", "assessment", "environment"}


class LedgerError(Exception):
    """A problem the person using the ledger can fix (bad input, missing key, failed signature). The command line
    turns it into an exit message; a program that uses ledger.py as a library catches it."""


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


def digest(path):
    """SHA-256 of a file; for a directory H("tree", {relative path: sha256}) over every file below it."""
    p = Path(path)
    if p.is_dir():
        return H("tree", {f.relative_to(p).as_posix(): sha_file(f) for f in sorted(p.rglob("*")) if f.is_file()})
    return sha_file(p)


def commitment(salt, dig):
    """Salted commitment to data with digest `dig` (FORMAT.md 3.4): hides small or guessable data."""
    return hashlib.sha256(("trust-ledger/0 commitment\0" + salt + "\0" + dig).encode("utf-8")).hexdigest()


def read_salt(path):
    salt = Path(path).read_text().strip()
    if not re.fullmatch(r"[0-9a-f]{64}", salt):
        raise ValueError(f"{path}: a salt is 64 lowercase hex digits")
    return salt


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
    """Sign with `ssh-keygen -Y sign -f keyfile`. keyfile is a private key file, or a public key file (*.pub): then
    only ssh-agent can hold the private key. A .pub file is copied to a scratch directory first, because ssh-keygen
    would otherwise fall back to the private key file next to it (and ask for its passphrase on a terminal)."""
    with tempfile.TemporaryDirectory() as d:
        keyfile = Path(keyfile)
        if keyfile.suffix == ".pub":
            shutil.copy(keyfile, Path(d) / "agent-key.pub")
            keyfile = Path(d) / "agent-key.pub"
        r = subprocess.run(["ssh-keygen", "-Y", "sign", "-f", str(keyfile), "-n", SIG_NAMESPACE],
                           input=message, capture_output=True)
    if r.returncode:
        raise LedgerError("ssh-keygen -Y sign failed: " + r.stderr.decode(errors="replace").strip())
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


def prose_list(items):
    """'a', 'a and b', 'a, b and c' (LaTeX: a tie before nothing, the items are typeset as given)."""
    items = list(items)
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1] if items else ""


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


def balance_envs(text):
    """Make the \\begin/\\end pairs of an excerpt match: an \\end without its \\begin is dropped, an unclosed \\begin is
    closed at the end (a paragraph boundary can cut through a proof or an itemize)."""
    stack, drop = [], []
    for m in re.finditer(r"\\(begin|end)\{([A-Za-z]+\*?)\}", text):
        if m.group(1) == "begin":
            stack.append(m.group(2))
        elif m.group(2) in stack:
            while stack.pop() != m.group(2):
                pass
        else:
            drop.append(m.span())
    for a, b in reversed(drop):
        text = text[:a] + text[b:]
    return text + "".join(f"\n\\end{{{name}}}" for name in reversed(stack))


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
        return balance_envs(retag_math(text[left:right])).strip()
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


# ---------------------------------------------------------------- adapter dumps (FORMAT.md section 2.6)
def check_dump(d):
    """Problems with an adapter dump; [] if it has the shape of FORMAT.md 2.6."""
    if not isinstance(d, dict) or not isinstance(d.get("nodes"), dict):
        return ['no "nodes" object']
    out = []
    for ref, n in d["nodes"].items():
        if not isinstance(n, dict):
            out.append(f"{ref}: not an object"); continue
        if not isinstance(n.get("kind"), str) or n["kind"] in CORE_KINDS:
            out.append(f"{ref}: kind must be a string other than the core kinds")
        if not isinstance(n.get("content"), dict):
            out.append(f"{ref}: content must be an object")
        if n.get("status") not in ADAPTER_STATUS:
            out.append(f"{ref}: status must be one of {', '.join(ADAPTER_STATUS)}")
        for x in n.get("deps", []):
            if x not in d["nodes"]:
                out.append(f"{ref}: dependency {x!r} is not in the dump")
        if not all(isinstance(r, str) and ":" in r for r in n.get("register", [])):
            out.append(f"{ref}: register items must be strings 'kind:name'")
        if "spec" in n and not isinstance(n["spec"], dict):
            out.append(f"{ref}: spec must be an object")
        for x in n.get("spec_deps", []):
            if "spec" not in d["nodes"].get(x, {}) or x not in n.get("deps", []):
                out.append(f"{ref}: spec dependency {x!r} must be a dependency with a spec")
        if not isinstance(n.get("result", False), bool) or not isinstance(n.get("info", {}), dict):
            out.append(f"{ref}: result must be true or false, info an object")
    if not isinstance(d.get("words", []), list) or not isinstance(d.get("environment", {}), dict):
        out.append("words must be a list, environment an object")
    if not isinstance(d.get("title", ""), str) or not isinstance(d.get("legend", ""), str) \
            or not isinstance(d.get("labels", {}), dict):
        out.append("title and legend must be strings, labels an object (word: text)")
    return out


# ---------------------------------------------------------------- git (optional: used when the project happens to be a repository)
GIT_OWN_FILES = re.compile(r"^ledger/(attestations\.toml|keys\.toml|snapshots/.*|lock[^/]*\.json)$")


def git(root, *args, check=False, binary=False):
    """(returncode, stdout) of `git -C root ...`; (127, '') if git is not installed."""
    try:
        r = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=not binary, timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return 127, b"" if binary else ""
    return r.returncode, r.stdout


def git_info(root):
    """{head, dirty} for the repository the project directory lies in, or None (no git, no repository, no commit yet).
    dirty: tracked files other than the ledger's own record files (attestations, keys, snapshots, lock files) differ from
    HEAD, i.e. what was attested is not exactly what HEAD contains."""
    rc, head = git(root, "rev-parse", "--verify", "-q", "HEAD")
    if rc != 0 or not head.strip():
        return None
    rc, names = git(root, "diff", "--name-only", "--relative", "HEAD", "--", ".")
    dirty = rc != 0 or any(n and not GIT_OWN_FILES.match(n) for n in names.splitlines())
    return dict(head=head.strip(), dirty=dirty)


def git_extract(root, commit, dest):
    """Unpack the project directory as it was in `commit` into dest. True on success."""
    rc, prefix = git(root, "rev-parse", "--show-prefix")
    if rc != 0:
        return False
    try:
        a = subprocess.Popen(["git", "-C", str(root), "archive", "--format=tar", f"{commit}:{prefix.strip()}" if prefix.strip() else commit],
                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        b = subprocess.run(["tar", "-x", "-C", str(dest)], stdin=a.stdout, capture_output=True)
        a.stdout.close()
        return a.wait() == 0 and b.returncode == 0
    except OSError:
        return False


# ---------------------------------------------------------------- loading
class Ledger:
    def __init__(self, root, paper=None):
        self.root = Path(root).resolve()
        self.dir = self.root / "ledger"
        cfgfile = self.dir / "ledger.toml"
        if not cfgfile.exists():
            raise LedgerError(f"{cfgfile} not found")
        self.cfg = tomllib.loads(cfgfile.read_text())
        self.paper = paper
        self.errors, self.warnings = [], []
        self.load_human()
        self.load_adapters()
        self.load_papers()
        self.build()

    def review_file(self, key, n):
        """The file the [review] template `key` (readings, extracts) names for claim n: the template filled with the
        claim's `review_name`, by default its name (a claim may keep its name while its back-translation and extract
        are a newer version made under another one). None without such a template."""
        t = self.cfg.get("review", {}).get(key)
        return t and self.root / t.format(claim=self.claims[n].get("review_name", n))

    def ev(self, c):
        """A claim's declared evidence type; without one, the weakest of the vocabulary."""
        return c.get("evidence", self.evidence_ids[-1])

    def load_vocabularies(self):
        """Evidence types ([[evidence]], strongest first) and checklist items ([checklist.ID]) of ledger.toml."""
        self.evidence = self.cfg.get("evidence") or DEFAULT_EVIDENCE
        if not all(isinstance(e, dict) and e.get("id") and e.get("name") for e in self.evidence):
            self.errors.append("ledger.toml: every [[evidence]] needs an `id` and a `name`")
            self.evidence = DEFAULT_EVIDENCE
        self.evidence_ids = [e["id"] for e in self.evidence]
        self.checklist = self.cfg.get("checklist", {})
        for k, item in self.checklist.items():
            if not item.get("text") or item.get("applies", "claim") not in ("claim", "hypothesis", "both"):
                self.errors.append(f"checklist {k}: needs a `text`; `applies` is claim, hypothesis or both")

    def checklist_problems(self, a):
        """Unknown or inapplicable checklist items of attestation a (none if the project defines no checklist)."""
        if not self.checklist:
            return []
        target = "hypothesis" if a.get("hypothesis") else "claim"
        return [x for x in a.get("checklist", []) if x not in self.checklist
                or self.checklist[x].get("applies", "claim") not in (target, "both")]

    # -- attesting (the library side of `attest`; raises LedgerError) --
    def make_attestation(self, person, level, claim=None, hypothesis=None, reason="", checklist=(), date=None):
        """The record of an attestation of a claim or of a hypothesis, bound to its current statement. Not yet
        signed or written."""
        if bool(claim) == bool(hypothesis):
            raise LedgerError("give exactly one of CLAIM and --hypothesis NAME")
        if level not in LEVELS:
            raise LedgerError(f"level {level!r} is not one of {', '.join(LEVELS)}")
        if hypothesis:
            if hypothesis not in self.scope_hyps:
                raise LedgerError(f"{hypothesis} is not a hypothesis of any result in this scope; known: "
                                  f"{', '.join(self.scope_hyps) or 'none'}")
            target, bound = dict(hypothesis=hypothesis), self.hspec[hypothesis]
        else:
            if claim not in self.claims:
                raise LedgerError(f"unknown claim {claim}")
            target, bound = dict(claim=claim), self.cspec[claim]
        if level == "yellow" and not reason:
            raise LedgerError("yellow needs --reason")
        rec = dict(**target, person=person, date=date or datetime.date.today().isoformat(), level=level,
                   reason=reason or "", checklist=list(checklist), bound=bound)
        bad = self.checklist_problems(rec)
        if bad:
            raise LedgerError(f"checklist item(s) {', '.join(bad)} not defined for this target in ledger.toml; defined: "
                              + ", ".join(f"{k} ({v.get('applies', 'claim')})" for k, v in self.checklist.items()))
        return rec

    def key_public(self, key_id, pub=None):
        """The public key line registered under `key_id` in ledger/keys.toml (or `pub`, a standalone file's key)."""
        pub = (self.keys.get(key_id) or {}).get("public") or pub
        if not pub:
            raise LedgerError(f"key {key_id!r} is not in ledger/keys.toml; register it with `addkey` or pass --pub FILE")
        return pub

    def sign_attestation(self, rec, key_id, keyfile, pub=None):
        """Sign rec (adds `key` and `sig`) with ssh-keygen -Y sign -f keyfile and check the signature against the
        registered public key. keyfile is a private key file, or the public key file when ssh-agent holds the private
        key. One signing call per attestation. Returns the public key line."""
        pub = self.key_public(key_id, pub)
        project = self.cfg.get("project", {}).get("name", "project")
        rec["key"] = key_id
        rec["sig"] = ssh_sign(keyfile, attestation_message(project, rec))
        if ssh_verify(pub, key_id, rec["sig"], attestation_message(project, rec)) is not True:
            for k in ("key", "sig"):
                rec.pop(k, None)
            raise LedgerError("the signature does not verify against the registered public key: wrong --sign file for this key?")
        return pub

    def append_attestation(self, rec, out=None, extra="", snapshot=True, git=True):
        """Append rec to ledger/attestations.toml (or `out`) as one whole record, under an exclusive lock so that
        concurrent writers cannot interleave. Unless `out` names a standalone file or snapshot is False, also record what
        the attestation bound to (`write_snapshot`); and, if the project is a git repository (and git is True), the commit it
        stood at as `git_head` and `git_dirty` (see git_info), which are not signed. Returns the path written."""
        import fcntl
        if snapshot and not out:
            self.write_snapshot(rec)
        if git and not out and "git_head" not in rec:
            info = git_info(self.root)
            if info:      # where the project stood; not signed and not hashed: a hint for later, never evidence
                rec["git_head"], rec["git_dirty"] = info["head"], info["dirty"]
        out = Path(out) if out else self.dir / "attestations.toml"
        text = extra + toml_record("[[attestation]]", rec)
        with open(out, "a", encoding="utf-8") as f:   # TOML is UTF-8; the length in bytes is what an undo needs
            fcntl.flock(f, fcntl.LOCK_EX)
            f.write(text)
            f.flush()
        return out

    # -- snapshots: what an attestation bound to, kept so that `diff` can show what changed since (not hashed, not in the root) --
    def snapshot_path(self, bound):
        return self.dir / "snapshots" / f"{bound}.json"

    def read_snapshot(self, bound):
        return json.loads(self.snapshot_path(bound).read_text(encoding="utf-8"))

    def _spec_closure(self, ids):
        seen, todo = set(), [i for i in ids if i in self.spec_payload]
        while todo:
            i = todo.pop()
            if i not in seen:
                seen.add(i)
                todo += [d for d in self.spec_deps.get(i, []) if d in self.spec_payload]
        return seen

    def snapshot_of(self, claim=None, hypothesis=None):
        """The current state of what an attestation of this claim (or hypothesis) binds to, as plain data: the statement
        text, and every evidence node with its spec hash and spec content (for Lean declarations: type and value), down to
        the declarations they depend on, plus the statements of the claims it uses."""
        if bool(claim) == bool(hypothesis):
            raise LedgerError("give exactly one of a claim and a hypothesis")
        nodes = {}
        if claim:
            if claim not in self.claims:
                raise LedgerError(f"unknown claim {claim}")
            c, prov = self.claims[claim], self.provenance_only(claim)
            ev = [i for i in sorted(self.deps["claim:" + claim])
                  if self.payload.get(i, {}).get("kind") not in ("claim", "reading", "assessment") and i not in prov]
            for i in ev:
                nodes[i] = dict(kind=self.payload[i]["kind"], spec=self.evidence_spec(i),
                                content=(self.spec_payload[i] if i in self.spec_payload else self.payload[i])["content"])
            uses = {u: dict(spec=self.cspec[u], text=self.stmt[u][0]) for u in c.get("uses", []) if u in self.claims}
            text, source, bound = self.stmt[claim][0], self.stmt[claim][1], self.cspec[claim]
            roots = ev
        else:
            if hypothesis not in self.scope_hyps:
                raise LedgerError(f"{hypothesis} is not a hypothesis of any result in this scope")
            meta = self.hypotheses.get(hypothesis, {})
            for x in sorted(meta.get("cites", [])):
                if "cite:" + x in self.full:
                    nodes["cite:" + x] = dict(kind="citation", spec=self.full["cite:" + x], content=self.payload["cite:" + x]["content"])
            roots = [self.hyp_node[hypothesis]] if hypothesis in self.hyp_node else []
            uses, (text, source), bound = {}, self.hstmt[hypothesis], self.hspec[hypothesis]
        for i in self._spec_closure(roots):
            nodes.setdefault(i, dict(kind=self.spec_payload[i]["kind"], spec=self.spec[i], content=self.spec_payload[i]["content"]))
        return dict(version=1, kind="claim" if claim else "hypothesis", name=claim or hypothesis, bound=bound,
                    text=text, source=source, nodes=nodes, uses=uses)

    def write_snapshot(self, rec):
        """Record the snapshot an attestation record binds to, if it is not there yet (the file is named by the bound
        hash, so one file serves every attestation of the same state). Returns the path, or None if rec does not bind to
        the current state (then there is nothing true to record)."""
        t = dict(claim=rec["claim"]) if rec.get("claim") else dict(hypothesis=rec.get("hypothesis"))
        snap = self.snapshot_of(**t)
        if snap["bound"] != rec.get("bound"):
            return None
        return self._write_snapshot_file(snap)

    def _write_snapshot_file(self, snap):
        p = self.snapshot_path(snap["bound"])
        if not p.exists():
            p.parent.mkdir(exist_ok=True)
            fd, tmp = tempfile.mkstemp(dir=p.parent, suffix=".tmp")      # a unique name: writers may run in parallel
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                f.write(json.dumps(snap, ensure_ascii=False, sort_keys=True))
            os.replace(tmp, p)                                          # atomic; the content is the same for every writer
        return p

    def recover_snapshots(self, targets=None, depth=8, dry_run=False, partial=False):
        """Snapshots of *stale* attestations that have none, rebuilt from the project's git history: find the commit that added
        the attestation record (or the `git_head` it names), unpack the project as it was, load it with this ledger.py, and
        take the snapshot of the claim there. It is written only if its bound hash is exactly the one the attestation names,
        so what is recovered is provably what was attested; the commit and up to `depth` first-parent ancestors are tried.
        Files that are not in git (a generated, ignored Lean dump, say) make the hash differ; then nothing is written, unless
        `partial`: the statement text of the commit that added the attestation is kept as an *unverified* snapshot (marked
        `partial`, no evidence nodes), good for showing how the text changed and for nothing else.
        Returns [{target, kind, bound, status ('recovered'|'would recover'|'partial'|'not found'), commit, note}]."""
        rc, _ = git(self.root, "rev-parse", "--git-dir")
        if rc != 0:
            raise LedgerError("this project is not in a git repository (or git is not installed): nothing to recover from")
        wanted = {}
        for a in self.attestations:
            kind = "claim" if a.get("claim") else "hypothesis"
            name, bound = a.get(kind), a.get("bound", "")
            if not bound or a.get("_sig") in ("invalid", "revoked"):
                continue
            if self.snapshot_path(bound).exists() and not self.read_snapshot(bound).get("partial"):
                continue
            cur = (self.cspec if kind == "claim" else self.hspec).get(name)
            if cur is None or cur == bound or (targets and name not in targets):
                continue            # not in this scope, or current (record_snapshots takes those), or not asked for
            wanted.setdefault(bound, dict(kind=kind, name=name, bound=bound, heads=[]))["heads"] += [a["git_head"]] if a.get("git_head") else []
        papers = list(self.cfg.get("paper", {}))
        trees, ledgers, results = {}, {}, []
        tmp = Path(tempfile.mkdtemp(prefix="ledger-git-"))

        def ledger_at(commit, paper):
            if (commit, paper) not in ledgers:
                if commit not in trees:
                    d = tmp / commit[:12]
                    d.mkdir(exist_ok=True)
                    trees[commit] = d if git_extract(self.root, commit, d) and (d / "ledger" / "ledger.toml").is_file() else None
                try:
                    ledgers[(commit, paper)] = Ledger(trees[commit], paper) if trees[commit] else None
                except Exception:       # an old tree that this ledger.py cannot read
                    ledgers[(commit, paper)] = None
            return ledgers[(commit, paper)]
        try:
            for bound, w in wanted.items():
                kind, name = w["kind"], w["name"]
                rc, found = git(self.root, "log", "--format=%H", f"-S{bound}", "--", "ledger")
                added = found.split()
                cands = list(w["heads"])
                if added:        # newest first: the last one added the record
                    rc, chain = git(self.root, "rev-list", "--first-parent", "-n", str(depth + 1), added[-1])
                    cands += chain.split()
                cands = list(dict.fromkeys(cands))
                if kind == "claim":
                    scopes = [self.claims[name].get("paper") if self.claims[name].get("paper") in papers else None]
                else:
                    scopes = list(dict.fromkeys([self.hypotheses.get(name, {}).get("paper")] + papers + [None]))
                res = dict(target=name, kind=kind, bound=bound, status="not found", commit="", note="")
                if not cands:
                    res["note"] = "the history has no commit that added this attestation (is it committed?)"
                for c in cands:
                    for sc in scopes:
                        L2 = ledger_at(c, sc)
                        if L2 is None:
                            continue
                        try:
                            snap = L2.snapshot_of(**{kind: name})
                        except LedgerError:
                            continue
                        if snap["bound"] == bound:
                            res.update(status="would recover" if dry_run else "recovered", commit=c)
                            if not dry_run:
                                self.snapshot_path(bound).unlink(missing_ok=True)       # replaces an earlier partial one
                                self._write_snapshot_file(snap)
                            break
                    if res["commit"]:
                        break
                if not res["commit"] and cands:
                    res["note"] = (f"tried {len(cands)} commit(s); none reproduces the attested state (generated or untracked inputs, "
                                   "or the state was never committed)")
                    if partial and not self.snapshot_path(bound).exists():
                        for c in cands:
                            L2 = next((ledgers[(c, sc)] for sc in scopes if ledgers.get((c, sc)) is not None), None)
                            if L2 is None or (name not in (L2.claims if kind == "claim" else L2.scope_hyps)):
                                continue
                            snap = L2.snapshot_of(**{kind: name})
                            snap = dict(snap, bound=bound, partial=True, commit=c, nodes={},
                                        uses={u: dict(spec="", text=v["text"]) for u, v in snap["uses"].items()})
                            res.update(status="partial" if not dry_run else "would keep partial", commit=c,
                                       note="statement text only, not verified against the attested hash (evidence is not in git)")
                            if not dry_run:
                                self._write_snapshot_file(snap)
                            break
                results.append(res)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        return results

    def record_snapshots(self, dry_run=False):
        """Snapshots for every claim and hypothesis that has a current attestation but no snapshot yet (attestations made
        before snapshots existed, or by hand). Returns the names recorded."""
        done = []
        for kind, names in (("claim", sorted(self.claims)), ("hypothesis", list(self.scope_hyps))):
            for n in names:
                cur = (self.cspec if kind == "claim" else self.hspec).get(n)
                if cur and not self.snapshot_path(cur).exists():
                    st = self.attestation_state(n) if kind == "claim" else self.hypothesis_state(n)
                    if any(ok for *_, ok in st):
                        if not dry_run:
                            self.write_snapshot({kind: n, "bound": cur})
                        done.append(n)
        return done

    def git_since(self, head, limit=300):
        """Files of the project that differ between commit `head` (named in an attestation record) and the working tree, or None
        without a head. {head, files, more, error}: error is set when the commit is not in this repository any more."""
        if not head:
            return None
        rc, out = git(self.root, "diff", "--name-only", "--relative", head, "--", ".")
        if rc != 0:
            return dict(head=head, files=[], more=0, error="that commit is not in this repository (history rewritten, or another clone)")
        files = [f for f in out.splitlines() if f and not GIT_OWN_FILES.match(f)]
        return dict(head=head, files=files[:limit], more=max(0, len(files) - limit), error="")

    def diff_since(self, claim=None, hypothesis=None):
        """What changed since the latest attestation that has a snapshot, as plain data. `available` is False when no
        attestation of this target has a snapshot (it was made before snapshots were recorded)."""
        kind, name = ("claim", claim) if claim else ("hypothesis", hypothesis)
        if name not in (self.claims if claim else self.scope_hyps):
            raise LedgerError(f"unknown {kind} {name}")
        recs = [a for a in self.attestations if a.get(kind) == name and a.get("_sig") not in ("invalid", "revoked")]
        if not recs:
            return dict(available=False, reason="this has no attestation")
        cur = self.snapshot_of(**{kind: name})
        ref = next((a for a in reversed(recs) if self.snapshot_path(a.get("bound", "")).exists()), None)
        if ref is None:
            a = recs[-1]
            return dict(available=False, current=a.get("bound") == cur["bound"], reason=
                        "no snapshot was recorded for any attestation of this; it cannot be compared (the snapshot is "
                        "written when an attestation is made, or by `ledger.py snapshot` while one is current)",
                        attestation=dict(person=a.get("person"), level=a.get("level"), date=a.get("date"), bound=a.get("bound")))
        # attestations of the same state (same bound) all describe it: take the commit from the newest one that names one
        hint = next((a for a in reversed(recs) if a.get("bound") == ref["bound"] and a.get("git_head")), ref)
        att = dict(person=ref.get("person"), level=ref.get("level"), date=ref.get("date"), bound=ref["bound"],
                   git_head=hint.get("git_head", ""), git_dirty=hint.get("git_dirty"))
        if ref["bound"] == cur["bound"]:
            return dict(available=True, current=True, attestation=att, text=dict(old=cur["text"], new=cur["text"], changed=False),
                        nodes=[], uses=[])
        old = self.read_snapshot(ref["bound"])
        partial = bool(old.get("partial"))
        nodes = []
        for i in ([] if partial else sorted(set(old["nodes"]) | set(cur["nodes"]))):
            o, n = old["nodes"].get(i), cur["nodes"].get(i)
            if o and n and o["spec"] == n["spec"]:
                continue
            nodes.append(dict(id=i, kind=(n or o)["kind"], change="added" if not o else "removed" if not n else "changed",
                              old=o and o["content"], new=n and n["content"],
                              content_same=bool(o and n and o["content"] == n["content"])))
        uses = []
        for u in sorted(set(old["uses"]) | set(cur["uses"])):
            o, n = old["uses"].get(u), cur["uses"].get(u)
            if o and n and (o["text"] == n["text"] if partial else o["spec"] == n["spec"]):
                continue
            uses.append(dict(name=u, change="added" if not o else "removed" if not n else "changed",
                             old_text=o and o["text"], new_text=n and n["text"]))
        return dict(available=True, current=False, attestation=att, git=self.git_since(att["git_head"]), unverified=(dict(commit=old.get("commit", "")) if partial else None),
                    text=dict(old=old["text"], new=cur["text"], changed=old["text"] != cur["text"]), nodes=nodes, uses=uses)

    # -- one claim in detail (what `why` prints; the web UI shows it next to the paper text and the Lean text) --
    def _dep_closure(self, start, skip=()):
        seen, todo = set(), list(start)
        while todo:
            i = todo.pop()
            if i in seen or i == self.env or i in skip:
                continue
            seen.add(i)
            todo += self.deps.get(i, [])
        return seen

    def why_data(self, n):
        """What claim n says and rests on, as plain data (`why` prints it)."""
        if n not in self.claims:
            raise LedgerError(f"unknown claim {n}")
        c = self.claims[n]
        prov = self.provenance_only(n)
        rests = self._dep_closure([i for i in self.deps["claim:" + n] if i not in prov])
        recorded = self._dep_closure(prov, skip=rests)
        label = lambda ids: [dict(provenance=self.payload[i]["provenance"], id=i) for i in sorted(ids)]
        return dict(name=n, statement=self.stmt[n][0], source=self.stmt[n][1], evidence=self.ev(c),
                    tools={name: self.adapter_status(name, n) for name in self.adapters if c.get(name)},
                    spec=self.cspec[n], rests_on=label(rests), recorded=label(recorded),
                    register=list(self.register[n]), step_of={m: list(ds) for m, ds in self.used_in(n).items()},
                    shares_label={lab: [x for x in ns if x != n] for lab, ns in self.split_labels().items() if n in ns},
                    attestations=[dict(person=p, level=lvl, date=date, current=cur)
                                  for p, lvl, date, cur in self.attestation_state(n)])

    def claim_detail(self, n):
        """why_data plus the texts a reviewer reads: the back-translation and the Lean statement extract named by
        the [review] templates (None where there is no template or no file), and the claims that use n."""
        d = self.why_data(n)
        c = self.claims[n]

        def read(key):
            try:
                f = self.review_file(key, n)
            except (KeyError, IndexError):
                f = None
            return (f.read_text(), str(f.relative_to(self.root))) if f and f.is_file() else (None, None)
        d["reading"], d["reading_file"] = read("readings")
        d["extract"], d["extract_file"] = read("extracts")
        d["uses"] = list(c.get("uses", []))
        d["used_by"] = sorted(m for m, x in self.claims.items() if n in x.get("uses", []))
        d["labels"] = c.get("labels") or ([c["label"]] if c.get("label") else [])
        d["paper"] = c.get("paper")
        d["bound"] = self.cspec[n]
        d["hypotheses"] = self.claim_hypotheses(n)
        st = self.assessment_state(n)
        d["assessment"] = dict(st, notes=self.assessments[n].get("notes", "")) if st else None
        return d

    def hypothesis_detail(self, h):
        """One hypothesis for a reader: its statement (from the paper by label, else the hand-written text), the citations
        it rests on with their fields (source URL and so on), what is attested, and the claims that are proved given it."""
        if h not in self.scope_hyps:
            raise LedgerError(f"{h} is not a hypothesis of any result in this scope; known: {', '.join(self.scope_hyps) or 'none'}")
        meta = self.hypotheses.get(h, {})
        text, source = self.hypothesis_statement(h, meta)
        cites = [dict(key=c, defined=c in self.citations, **{k: v for k, v in (self.citations.get(c) or {}).items() if k != "key"})
                 for c in meta.get("cites", [])]
        return dict(name=h, label=meta.get("label"), paper=meta.get("paper"), statement=text, source=source, cites=cites,
                    bound=self.hspec[h], known_theorem=self.known_theorem(h),
                    checklist={k: v.get("text", "") for k, v in self.checklist.items()
                               if v.get("applies", "claim") in ("hypothesis", "both")},
                    attestations=[dict(person=p, level=lvl, date=date, current=cur,
                                       signature=self.signature_of(h, p, "hypothesis"))
                                  for p, lvl, date, cur in self.hypothesis_state(h)],
                    used_by=sorted(n for n in self.claims if h in self.claim_hypotheses(n)))

    # -- assessments: a model's comparison of paper text, Lean statement and back-translation (FORMAT.md 3.3) --
    def reading_hash(self, n):
        """sha256 of the back-translation file of claim n ('' if there is none)."""
        if not self.cfg.get("review", {}).get("readings"):
            return ""
        rp = self.review_file("readings", n)
        return sha_file(rp) if rp and rp.is_file() else ""

    def assessment_state(self, n):
        """None without an assessment, else {verdict, model, date, state, why}. state is `current` (it names the claim's
        present spec hash, and the present back-translation if it names one), `outdated` (it names another: the statement or
        what it rests on changed since, or the back-translation was redone) or `unbound` (it names none; written before
        assessments recorded what they judged, so nothing can be said)."""
        a = self.assessments.get(n)
        if a is None:
            return None
        why = []
        if not a.get("spec"):
            state = "unbound"
        else:
            if a["spec"] != self.cspec.get(n):
                why.append("the claim's statement or what it rests on changed since")
            if a.get("reading") and a["reading"] != self.reading_hash(n):
                why.append("the back-translation changed since")
            state = "outdated" if why else "current"
        return dict(verdict=a.get("verdict", ""), model=a.get("model", ""), date=a.get("date", ""), state=state, why=why)

    def audit_assessments(self, targets=None):
        """For assessments that name no state (`unbound`): did what they compared change since they were written, according to
        git? The commit is the last one that touched the assessment's table; at that commit the project is unpacked and loaded,
        and compared with now: the statement text from the paper, the claim's Lean references (and `review_name`), the Lean
        statement extract and the back-translation. [{claim, date, commit, state, changes, note}], state `unchanged` (nothing
        of those four differs: probably still describes the claim, which only a person can confirm), `changed`, or `unknown`.
        Needs git; reads the history only. What the extract does not contain (a definition changed elsewhere) is not seen."""
        rc, _ = git(self.root, "rev-parse", "--git-dir")
        if rc != 0:
            raise LedgerError("this project is not in a git repository (or git is not installed): nothing to compare with")
        files, length = {}, {}
        for f in sorted(self.dir.glob("*.toml")):
            for n, (a, b) in assessment_blocks(f.read_text(encoding="utf-8")).items():
                files[n], length[n] = f, max(1, b - a - 1)
        rows, trees, ledgers = [], {}, {}
        tmp = Path(tempfile.mkdtemp(prefix="ledger-audit-"))
        rel = lambda p: p.relative_to(self.root).as_posix() if p else ""
        read = lambda p: p.read_text(encoding="utf-8", errors="replace") if p and p.is_file() else None
        try:
            for n in sorted(self.assessments):
                if n not in self.claims or (targets and n not in targets):
                    continue
                st = self.assessment_state(n)
                if st["state"] != "unbound":
                    continue
                row = dict(claim=n, date=st["date"], commit="", state="unknown", changes=[], note="")
                rc, out = git(self.root, "log", "-n1", "--format=%H", "-L", f"/^\\[assessment\\.{re.escape(n)}\\]/,+{length[n]}:{rel(files[n])}", "-s")
                commit = out.split()[0] if rc == 0 and out.split() else ""
                if not commit:
                    row["note"] = "the history does not say when this assessment was written (not committed?)"
                    rows.append(row)
                    continue
                row["commit"] = commit
                if commit not in trees:
                    d = tmp / commit[:12]
                    d.mkdir(exist_ok=True)
                    trees[commit] = d if git_extract(self.root, commit, d) and (d / "ledger" / "ledger.toml").is_file() else None
                L2 = None
                for scope in dict.fromkeys([self.paper, None]):          # the paper may not have been configured yet: then all
                    if (commit, scope) not in ledgers:
                        try:
                            ledgers[(commit, scope)] = Ledger(trees[commit], scope) if trees[commit] else None
                        except Exception:
                            ledgers[(commit, scope)] = None
                    if ledgers[(commit, scope)] is not None and n in ledgers[(commit, scope)].claims:
                        L2 = ledgers[(commit, scope)]
                        break
                if L2 is None or n not in L2.claims:
                    row["note"] = "the project at that commit cannot be loaded, or did not have this claim"
                    rows.append(row)
                    continue
                c1, c2 = L2.claims[n], self.claims[n]
                if L2.stmt[n][0] != self.stmt[n][0]:
                    row["changes"].append("paper statement")
                if (c1.get("lean"), c1.get("review_name")) != (c2.get("lean"), c2.get("review_name")):
                    row["changes"].append("Lean references or review_name")
                if read(L2.review_file("extracts", n)) != read(self.review_file("extracts", n)):
                    row["changes"].append("Lean statement extract")
                if read(L2.review_file("readings", n)) != read(self.review_file("readings", n)):
                    row["changes"].append("back-translation")
                row["state"] = "changed" if row["changes"] else "unchanged"
                rows.append(row)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        return rows

    # -- structured status (what `status` prints; `status --json` prints it as JSON) --
    def status_data(self):
        """Everything `status` reports, as plain data: claims, hypotheses, root, messages (warnings and errors in
        the order `status` prints them) and the number of stale attestations."""
        tools = self.tools_in_scope()
        claims, stale = [], 0
        for n in sorted(self.claims):
            c = self.claims[n]
            att = [dict(person=p, level=lvl, date=date, current=cur, signature=self.signature_of(n, p))
                   for p, lvl, date, cur in self.attestation_state(n)]
            stale += sum(not a["current"] for a in att)
            ts = {}
            for t in tools:
                status, word = self.adapter_state(t, n)
                hs = self.claim_hypotheses(n)
                known = [sum(self.known_theorem(h) for h in hs), len(hs)] if status == "conditional" and hs else None
                ts[t] = dict(status=status, word=word, known_theorems=known)
            claims.append(dict(name=n, evidence=self.ev(c), statement=self.stmt[n][1], tools=ts,
                               attestations=att, register=len(self.register[n]), bound=self.cspec.get(n),
                               labels=c.get("labels") or ([c["label"]] if c.get("label") else []),
                               paper=c.get("paper"), uses=list(c.get("uses", [])),
                               hypotheses=self.claim_hypotheses(n), assessment=self.assessment_state(n)))
        hyps = []
        for h in self.scope_hyps:
            meta = self.hypotheses.get(h, {})
            st = self.hypothesis_state(h)
            stale += any(not cur for *_, cur in st)
            hyps.append(dict(name=h, label=meta.get("label"), cites=list(meta.get("cites", [])), bound=self.hspec.get(h),
                             known_theorem=self.known_theorem(h),
                             attestations=[dict(person=p, level=lvl, date=date, current=cur,
                                                signature=self.signature_of(h, p, "hypothesis"))
                                           for p, lvl, date, cur in st]))
        notes, messages = [], []
        if self.paper and self.cfg.get("generated", {}).get("dirs"):
            rf = self.root / self.cfg["generated"]["dirs"][0] / f"ledger-{self.paper}-root.tex"
            if rf.exists():
                m = re.search(r"\\def\\LedgerRoot\{([0-9a-f]+)\}", rf.read_text())
                if not m or m.group(1) != self.root_hash:
                    notes.append(f"note: {rf.name} shows an older root: run `ledger.py -P {self.paper} tex` before building the paper")
        for lab, ns in self.split_labels().items():
            messages.append(f"warning: {lab} is carried by {len(ns)} claims ({', '.join(ns)}); state the whole result as one Lean "
                            "theorem and keep the label on that claim only")
        unc = self.uncovered()
        if unc:
            messages.append(f"warning: {len(unc)} labelled results are not in the ledger: {', '.join(unc[:12])}"
                            + (" ..." if len(unc) > 12 else ""))
        for name, u in self.unresolved.items():
            if u:
                messages.append(f"warning: paper {name}: could not resolve {', '.join(u)}")
        for n in sorted(self.claims):
            st = self.assessment_state(n)
            if st and st["state"] == "outdated":
                messages.append(f"warning: the assessment of {n} is outdated: {'; '.join(st['why'])}")
        messages += ["warning: " + w for w in self.warnings]
        messages += ["error: " + e for e in self.errors]
        return dict(ledger_tool=__version__, format=FORMAT_VERSION, paper=self.paper, root=self.root_hash, tools=tools,
                    claims=claims, hypotheses=hyps, stale=stale, notes=notes, messages=messages,
                    ok=not self.errors, uncovered=unc)

    def load_human(self):
        self.load_vocabularies()
        self.claims, self.citations, self.assertions, self.attestations, self.keys = {}, {}, {}, [], {}
        self.hypotheses, self.assessments = {}, {}
        self.sources, self.steps, self.checks = {}, {}, {}
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
            self.sources.update(t.get("source", {}))
            self.steps.update(t.get("step", {}))
            self.checks.update(t.get("check", {}))
        for n, st in self.steps.items():
            if bool(st.get("command")) == bool(st.get("manual")):
                self.errors.append(f"step {n}: needs exactly one of `command` and `manual`")
            elif st.get("manual") and not st.get("person"):
                self.errors.append(f"step {n}: a manual step needs the `person` who did it")
            if st.get("compare", "bytes") not in ("bytes", "none"):
                self.errors.append(f"step {n}: compare is `bytes` (default) or `none` (outputs differ from run to run)")
        for n, ch in self.checks.items():
            if not ch.get("command"):
                self.errors.append(f"check {n}: needs a `command`")
        for n, c in self.claims.items():
            if self.ev(c) not in self.evidence_ids:
                self.errors.append(f"claim {n}: unknown evidence type {c['evidence']!r} "
                                   f"(known: {', '.join(self.evidence_ids)})")
        self.apply_scope()
        for a in self.attestations:
            if bool(a.get("claim")) == bool(a.get("hypothesis")):
                self.errors.append(f"attestation by {a.get('person')}: needs exactly one of `claim` and `hypothesis`")
            if a.get("level") not in LEVELS:
                self.errors.append(f"attestation on {a.get('claim')}: unknown level {a.get('level')!r}")
            elif a["level"] == "yellow" and not a.get("reason"):
                self.errors.append(f"attestation on {a.get('claim')}: yellow needs a reason")
            for x in self.checklist_problems(a):
                self.errors.append(f"attestation by {a.get('person')} on {a.get('claim') or a.get('hypothesis')}: "
                                   f"checklist item {x!r} is not defined for it in ledger.toml")
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
            # relative to the project root, also for files outside it (`../`), so that the root does not depend
            # on where the project is checked out
            rel = lambda f: Path(os.path.relpath(f, self.root)).as_posix()
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
        # The paper that states the lemma is not in this scope (`-P other`): the hand-written `text`, if the entry
        # has one, stands in for it. Without that fallback the label is searched in the papers of the scope.
        if lab and meta.get("paper") and meta["paper"] not in self.parsed and meta.get("text"):
            return meta["text"], "manual"
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

    def load_adapters(self):
        """Adapter dumps (FORMAT.md 2.6): self.adapters[name] = {prefix, nodes: {reference: node}, words,
        environment}; claim references ending in `*` are expanded here."""
        self.adapters = {}
        for old in ("lean", "proverif"):
            if old in self.cfg:
                self.errors.append(f"ledger.toml: the [{old}] section is now [adapter.{old}], with a dump in the adapter "
                                   f"format (docs/FORMAT.md 2.6; converter/extractor adapters/{old}.py)")
        for name, ac in self.cfg.get("adapter", {}).items():
            if name in CLAIM_FIELDS or name == "checks":
                self.errors.append(f"adapter {name!r}: the name is a claim field or a built-in adapter")
                continue
            self.load_dump(name, ac, "ledger.py extract")
        if self.checks:  # built-in adapter: results of [check.*], written by `ledger.py check`
            self.load_dump("checks", dict(prefix="check:", dump="checks.json"), "ledger.py check")
        for c in self.claims.values():
            for name, a in self.adapters.items():
                if name in c:
                    c[name] = self.expand(a, c[name])
        lean = self.adapters.get("lean", {}).get("nodes", {})
        self.decls = {n: nd["content"] for n, nd in lean.items()}  # Lean declarations, for the review packet

    def load_dump(self, name, ac, hint):
        a = self.adapters[name] = dict(prefix=ac.get("prefix", name + ":"), nodes={}, words=[], environment=None,
                                       title=name, labels={}, legend="")
        p = self.dir / ac.get("dump", name + ".json")
        if not p.exists():
            if any(c.get(name) for c in self.claims.values()):
                self.errors.append(f"{p} missing: run `{hint}`")
            return
        d = json.loads(p.read_text())
        problems = check_dump(d)
        self.errors += [f"{p.name}: {x}" for x in problems]
        if problems:
            return  # an invalid dump contributes nothing
        a.update(nodes=d["nodes"], words=d.get("words", []), environment=d.get("environment"),
                 title=d.get("title", name), labels=d.get("labels", {}), legend=d.get("legend", ""))
        if d.get("env_hash") and name != "checks" and d["env_hash"] != self.env_hash():  # checks: per check, above
            self.errors.append(f"{p.name} is older than the sources it was extracted from "
                               f"(environment files changed): run `{hint}`")

    @staticmethod
    def expand(a, refs):
        """`Prefix*` stands for every result node (`result: true`) of the dump whose reference starts with Prefix."""
        out = []
        for x in refs:
            if x.endswith("*"):
                out += sorted(r for r, nd in a["nodes"].items() if r.startswith(x[:-1]) and nd.get("result"))
            else:
                out.append(x)
        return out

    # -------------------------------------------------------- graph
    def build(self):
        payload, deps = {}, {}  # full graph
        env_files = {f: sha_file(self.root / f) for f in self.env_files()}
        env = "env:" + self.cfg.get("project", {}).get("name", "project")
        payload[env] = dict(kind="environment", provenance="computed", content=dict(
            files=env_files, adapters={k: a["environment"] for k, a in sorted(self.adapters.items()) if a["environment"]}))
        deps[env] = []
        self.spec_payload, self.spec_deps = {}, {}
        for n, c in self.citations.items():
            i = "cite:" + n
            payload[i] = dict(kind="citation", provenance="asserted",
                              content=dict(key=c.get("key", n), statement=c.get("statement", ""), source=c.get("source", "")))
            deps[i] = []
        for n, a in self.assertions.items():
            i = "assert:" + n
            payload[i] = dict(kind="assertion", provenance="asserted", content=dict(claim=a["claim"], text=a["text"]))
            deps[i] = []
        self.build_data(payload, deps, env)
        for n, c in self.claims.items():
            for f in c.get("files", []) + c.get("provenance", []):
                self.file_node(payload, deps, f, f"claim {n}")
        for name, a in self.adapters.items():  # every node of every dump; what no root rests on is dropped below
            for ref, nd in a["nodes"].items():
                i = a["prefix"] + ref
                payload[i] = dict(kind=nd["kind"], provenance="computed", content=nd["content"])
                # tools rest on their environment; a check (a script of the project) only if it declares it
                uses_env = name != "checks" or self.checks.get(ref, {}).get("environment", False)
                deps[i] = sorted({a["prefix"] + x for x in nd.get("deps", [])} | ({env} if uses_env else set()))
                if "spec" in nd:
                    self.spec_payload[i] = dict(kind=nd["kind"], content=nd["spec"])
                    self.spec_deps[i] = sorted({a["prefix"] + x for x in nd.get("spec_deps", [])})
            for n, c in self.claims.items():
                for ref in c.get(name, []):
                    if ref not in a["nodes"]:
                        self.errors.append(f"claim {n}: {name} reference {ref!r} not in dump")
        for ref, ch in self.checks.items():  # a check rests on its inputs; a result for other inputs is outdated
            i = "check:" + ref
            if i not in payload:
                continue
            ins = {x: self.input_hash(x) for x in ch.get("inputs", [])}
            for x in ins:
                deps[i].append(x if x.startswith("source:") else self.file_node(payload, deps, x, f"check {ref}") or x)
            deps[i] = sorted(set(d for d in deps[i] if d in payload))
            got = self.adapters["checks"]["nodes"][ref]["content"]
            env_now = self.env_hash() if ch.get("environment") else None
            if (got.get("inputs") != ins or got.get("command") != ch["command"] or got.get("code") != self.code_hashes(ch)
                    or got.get("environment") != env_now):
                self.errors.append(f"check {ref}: the recorded result is for other inputs or another version of the "
                                   "check: run `ledger.py check`")
        for n, c in self.claims.items():
            for x in c.get("sources", []):
                if x not in self.sources:
                    self.errors.append(f"claim {n}: unknown source {x}")
            for f in sorted(set(c) - CLAIM_FIELDS - set(self.adapters)):
                self.errors.append(f"claim {n}: unknown field {f!r} (no adapter of that name is configured)")
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
            self.stmt[n] = self.statement(n, c)
        # hypotheses the in-scope results are proved given: `hyp:` register items of the adapter nodes claims refer to
        self.scope_hyps = sorted({x[4:] for c in self.claims.values() for name, a in self.adapters.items()
                                  for ref in c.get(name, []) for x in a["nodes"].get(ref, {}).get("register", [])
                                  if x.startswith("hyp:")})
        self.hyp_node = {}  # the node that states a hypothesis, if an adapter has one (Lean: its definition)
        for h in self.scope_hyps:
            for a in self.adapters.values():
                if h in a["nodes"]:
                    self.hyp_node[h] = a["prefix"] + h
                    break
        self.hstmt = {}
        for h in self.scope_hyps:
            meta = self.hypotheses.get(h, {})
            self.hstmt[h] = self.hypothesis_statement(h, meta)
            payload["hyp:" + h] = dict(kind="hypothesis", provenance="asserted", content=dict(
                name=h, label=meta.get("label", ""), text=self.hstmt[h][0], source=self.hstmt[h][1],
                cites=sorted(meta.get("cites", [])), note=meta.get("note", "")))
            deps["hyp:" + h] = sorted(["cite:" + x for x in meta.get("cites", []) if x in self.citations]
                                      + ([self.hyp_node[h]] if h in self.hyp_node else []))
            for x in meta.get("cites", []):
                if x not in self.citations:
                    self.errors.append(f"hypothesis {h}: unknown citation {x}")
        for n, c in self.claims.items():
            i = "claim:" + n
            d = ["file:" + f for f in c.get("files", []) + c.get("provenance", []) if "file:" + f in payload]
            d += ["source:" + x for x in c.get("sources", []) if "source:" + x in payload]
            d += [i for i in self.adapter_ids(c) if i in payload]
            for x in c.get("cites", []):
                if x in self.citations:
                    d.append("cite:" + x)
                else:
                    self.errors.append(f"claim {n}: unknown citation {x}")
            d += ["assert:" + a for a, v in self.assertions.items() if v["claim"] == n]
            rv = self.cfg.get("review", {})
            if rv.get("readings"):  # a model's back-translation of the Lean statement: an aid, never part of the spec hash
                rp = self.review_file("readings", n)
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
                    notes=a.get("notes", ""), **{k: a[k] for k in ("spec", "reading") if a.get(k)}))
                deps["assess:" + n] = []
                d.append("assess:" + n)
            for u in c.get("uses", []):
                if u in self.claims:
                    d.append("claim:" + u)
                else:
                    self.errors.append(f"claim {n}: unknown claim {u} in uses")
            payload[i] = dict(kind="claim", provenance="asserted", content=dict(
                text=self.stmt[n][0], source=self.stmt[n][1], label=c.get("label", ""), evidence=self.ev(c)))
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
            prov = self.provenance_only(n)
            cp[n] = dict(text=self.stmt[n][0],
                         evidence=[[i, self.evidence_spec(i)] for i in sorted(deps["claim:" + n])
                                   if payload.get(i, {}).get("kind") not in ("claim", "reading", "assessment") and i not in prov])
            cd[n] = [u for u in c.get("uses", []) if u in self.claims]
        self.cspec = merkle(cp, cd, "claim-spec")
        self.hspec = {h: H("hyp-spec", dict(text=self.hstmt[h][0], stated=self.spec.get(self.hyp_node.get(h), ""),
                                           cites=[[x, self.full["cite:" + x]] for x in sorted(self.hypotheses.get(h, {}).get("cites", []))
                                                  if "cite:" + x in self.full]))
                      for h in self.scope_hyps}
        self.root_hash = H("root", [[i, self.full[i]] for i in sorted(payload)
                                    if payload[i]["kind"] in ROOT_KINDS])
        self.register = self.compute_register()
        rank = {e: k for k, e in enumerate(self.evidence_ids)}  # 0 = strongest
        for n, c in self.claims.items():
            for u in c.get("uses", []):
                if u in self.claims and rank.get(self.ev(self.claims[u]), 0) > rank.get(self.ev(c), 0):
                    self.warnings.append(f"claim {n} declares {self.ev(c)} but uses {u}, which declares "
                                         f"{self.ev(self.claims[u])}: a result is no stronger than what it rests on")

    # -------------------------------------------------------- data, steps, checks (FORMAT.md 3.4)
    def provenance_only(self, n):
        """File nodes a claim records only as provenance: not in its spec hash, not in its register."""
        c = self.claims[n]
        return {"file:" + f for f in c.get("provenance", [])} - {"file:" + f for f in c.get("files", [])}

    def evidence_spec(self, i):
        """What an attestation binds to for evidence node i: its spec if it has one; for a file, its content alone
        (the node hash without the step that produced it: a person attests what the file shows, not how it was
        made); otherwise its full hash."""
        if i in self.spec:
            return self.spec[i]
        if self.payload.get(i, {}).get("kind") == "file":
            return merkle({i: self.payload[i]}, {i: []}, "node")[i]
        return self.full[i]

    def file_node(self, payload, deps, f, who):
        """Node id of the file (or directory) f, created on first use; it rests on the step that produces it."""
        i = "file:" + f
        if i not in payload:
            if not (self.root / f).exists():
                self.errors.append(f"{who}: file {f} not found")
                return None
            payload[i] = dict(kind="file", provenance="computed", content=dict(path=f, sha256=digest(self.root / f)))
            deps[i] = ["step:" + self.producer[f]] if f in self.producer else []
        return i

    def code_hashes(self, x):
        return {f: digest(self.root / f) if (self.root / f).exists() else "missing" for f in sorted(x.get("code", []))}

    def input_hash(self, x):
        """Current hash of a step or check input: a source's recorded value, or a file's digest."""
        if x.startswith("source:"):
            return self.source_value.get(x[7:], "unknown")
        return digest(self.root / x) if (self.root / x).exists() else "missing"

    def build_data(self, payload, deps, env):
        self.producer, self.source_value = {}, {}
        for n, st in self.steps.items():
            for f in st.get("outputs", []):
                if f in self.producer:
                    self.errors.append(f"file {f} is an output of two steps: {self.producer[f]} and {n}")
                self.producer.setdefault(f, n)
        for n, src in self.sources.items():
            meta = {k: src[k] for k in ("path", "url", "doi", "retrieved", "license", "note") if k in src}
            path = self.root / src["path"] if src.get("path") else None
            recorded = src.get("commitment") or src.get("sha256")
            if recorded:  # the hash is recorded: the data may be absent (not published), so the node is asserted
                key = "commitment" if src.get("commitment") else "sha256"
                payload["source:" + n] = dict(kind="source", provenance="asserted", content=dict(meta, name=n, **{key: recorded}))
                if path and path.exists():  # the author's copy: check it against the record
                    salt = self.root / src["salt_file"] if src.get("salt_file") else None
                    if key == "sha256" and digest(path) != recorded:
                        self.errors.append(f"source {n}: {src['path']} differs from the recorded sha256")
                    elif key == "commitment" and salt and salt.exists() and commitment(read_salt(salt), digest(path)) != recorded:
                        self.errors.append(f"source {n}: {src['path']} and its salt do not match the recorded commitment")
            elif path and path.exists():
                if src.get("salt_file"):
                    self.errors.append(f"source {n}: record its commitment (`ledger.py commitment {src['path']} "
                                       f"--salt-file {src['salt_file']}`), or drop salt_file")
                payload["source:" + n] = dict(kind="source", provenance="computed", content=dict(meta, name=n, sha256=digest(path)))
            else:
                self.errors.append(f"source {n}: needs a `path` that exists, or a recorded `sha256` or `commitment`")
                continue
            deps["source:" + n] = []
            self.source_value[n] = recorded or payload["source:" + n]["content"]["sha256"]
        for n, st in self.steps.items():
            i = "step:" + n
            payload[i] = dict(kind="step", provenance="asserted", content=dict(
                {k: st[k] for k in ("command", "manual", "person", "note", "compare", "environment") if k in st},
                name=n, outputs=sorted(st.get("outputs", [])), code=self.code_hashes(st)))
            d = [env] if st.get("environment", False) else []   # a step rests on the environment only if it says so
            for x in st.get("inputs", []):
                if x.startswith("source:"):
                    if x[7:] in self.sources:
                        d.append(x)
                    else:
                        self.errors.append(f"step {n}: unknown source {x[7:]}")
                else:
                    d.append(self.file_node(payload, deps, x, f"step {n}"))
            deps[i] = sorted(set(x for x in d if x))
            for f in st.get("code", []):
                if not (self.root / f).exists():
                    self.errors.append(f"step {n}: code file {f} not found")

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
            r |= {"hyp:cited:" + x for x in c.get("cites", [])}
            for name, a in self.adapters.items():
                r |= {x for ref in c.get(name, []) for x in a["nodes"].get(ref, {}).get("register", [])}
            r |= {"assertion:" + a for a, v in self.assertions.items() if v["claim"] == n}
            prov = self.provenance_only(n)  # recorded, not relied on
            seen, todo = set(), [i for i in self.deps["claim:" + n] if i not in prov]  # the data chain: files, steps, sources, checks
            while todo:
                i = todo.pop()
                kind = self.payload.get(i, {}).get("kind")
                if i in seen or kind not in ("file", "step", "source", "check"):
                    continue
                seen.add(i)
                todo += self.deps.get(i, [])
                if kind == "source":
                    r.add("data:" + i[7:])
                elif kind == "step" and self.payload[i]["content"].get("manual"):
                    r.add("manual:" + i[5:])
            if not c.get("files") and not c.get("sources") and not any(c.get(name) for name in self.adapters):
                r.add("evidence:none")
            own[n] = r
        self.own_register = own
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
        """'ok', 'assumes', 'axioms', 'sorry', 'missing' or '-': the words adapters/lean.py gives its nodes."""
        return self.adapter_status("lean", n)

    def adapter_ids(self, c):
        """Node ids of the adapter references of claim c."""
        return [a["prefix"] + ref for name, a in self.adapters.items() for ref in c.get(name, [])]

    def adapter_state(self, name, n):
        """(status, word) of the worst node among claim n's references into adapter `name`; ('missing', 'missing')
        if a reference is not in the dump, ('none', '-') if the claim has none."""
        a, refs = self.adapters.get(name), self.claims[n].get(name, [])
        if not refs or a is None:
            return "none", "-"
        nodes = [a["nodes"].get(r) for r in refs]
        if any(x is None for x in nodes):
            return "missing", "missing"
        rank = lambda x: (ADAPTER_STATUS.index(x["status"]),
                          a["words"].index(x["word"]) if x.get("word") in a["words"] else -1)
        worst = max(nodes, key=rank)  # equal status: the later of the dump's `words` (best to worst)
        return worst["status"], worst.get("word", worst["status"])

    def adapter_status(self, name, n):
        """The word (else the status) of claim n's worst reference into adapter `name`; 'missing' or '-'."""
        return self.adapter_state(name, n)[1]

    def tools_in_scope(self):
        """Adapters that at least one claim in scope refers to, in configuration order (checks last)."""
        return [name for name in self.adapters if any(c.get(name) for c in self.claims.values())]

    def proverif_status(self, n):
        """'ok' (every query true), 'false' (an attack was found), 'unproved' ('cannot be proved'),
        'missing' or '-': the words adapters/proverif.py gives its nodes."""
        return self.adapter_status("proverif", n)

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

    def split_labels(self):
        """Paper labels carried by more than one claim in scope, {label: [claims]}. Every paper result should be
        stated by one Lean theorem on one claim (a conjunction if the result has several parts); the theorems for
        the parts are then steps of its proof (see used_in) and need no attestation of their own for that label."""
        m = {}
        for n, c in self.claims.items():
            for lab in (c.get("labels") or ([c["label"]] if c.get("label") else [])):
                m.setdefault(lab, []).append(n)
        return {lab: sorted(ns) for lab, ns in m.items() if len(ns) > 1}

    def closure(self, ids):
        """Adapter nodes the given ones rest on (in Lean: statements and proofs), transitively."""
        seen, todo = set(), list(ids)
        while todo:
            x = todo.pop()
            if x in seen or x not in self.deps or x == self.env:
                continue
            seen.add(x)
            todo += self.deps[x]
        return seen

    def register_origin(self, n, item):
        """The claim, n itself or one reached through `uses`, whose own register contributes `item` to Reg(n)."""
        todo, seen = [n], set()
        while todo:
            m = todo.pop(0)
            if m in seen or m not in self.claims:
                continue
            seen.add(m)
            if item in self.own_register.get(m, ()):
                return m
            todo += self.claims[m].get("uses", [])
        return None

    def used_in(self, n):
        """Claims whose adapter nodes rest on one of claim n's (in Lean: use it in their proofs):
        {claim: [references]}. Claim n is then a step of those claims."""
        own = set(self.adapter_ids(self.claims[n]))
        ref = {a["prefix"] + r: r for a in self.adapters.values() for r in a["nodes"]}
        out = {}
        for m, c in self.claims.items():
            theirs = set(self.adapter_ids(c))
            if m == n or not theirs:
                continue
            hit = sorted(ref[i] for i in own & (self.closure(theirs) - theirs))
            if hit:
                out[m] = hit
        return out

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

    def signature_of(self, n, person, target="claim"):
        """Signature state of the latest counted attestation by `person` on claim n (target="hypothesis": on
        hypothesis n)."""
        latest = None
        for a in self.attestations:
            if a.get(target) == n and a.get("person", "?") == person and a.get("_sig") not in ("invalid", "revoked"):
                latest = a
        return latest.get("_sig", "unsigned") if latest else "unsigned"

    def lock(self):
        return dict(format=FORMAT_VERSION, tool=__version__, root=self.root_hash,
                    nodes={i: dict(kind=p["kind"], full=self.full[i]) for i, p in sorted(self.payload.items())},
                    claims={n: dict(spec=self.cspec[n], register=self.register[n]) for n in sorted(self.claims)},
                    hypotheses={h: dict(spec=self.hspec[h]) for h in self.scope_hyps})


# ---------------------------------------------------------------- commands
def cmd_status(L, args):
    d = L.status_data()
    if getattr(args, "json", False):
        print(json.dumps(d, indent=2, ensure_ascii=False))
        return 1 if not d["ok"] or (args.strict and d["stale"]) else 0
    word = {"green": "GREEN", "yellow": "YELLOW", "conjecture": "CONJECTURE"}
    tools = d["tools"]
    rows = [("claim", "evid", "stmt", *tools, "attestation", "register")]
    for c in d["claims"]:
        att = [f"{word.get(a['level'], a['level'])} {a['person']} {'current' if a['current'] else 'STALE'}"
               for a in c["attestations"]]
        cells = []
        for t in tools:
            w, k = c["tools"][t]["word"], c["tools"][t]["known_theorems"]
            if c["tools"][t]["status"] == "conditional" and k and k[0]:
                w += f" ({k[0]}/{k[1]} known thm.)"
            cells.append(w)
        rows.append((c["name"], c["evidence"], c["statement"], *cells, "; ".join(att) or "none", str(c["register"])))
    w = [max(len(r[i]) for r in rows) for i in range(len(rows[0]))]
    for r in rows:
        print("  ".join(c.ljust(w[i]) for i, c in enumerate(r)).rstrip())
    if d["hypotheses"]:
        print("\nhypotheses (results are proved given these):")
        for h in d["hypotheses"]:
            att = "; ".join(f"{word.get(a['level'], a['level'])} {a['person']} {'current' if a['current'] else 'STALE'}"
                            for a in h["attestations"]) or "not attested"
            print(f"  {h['name']}  [{h['label'] or 'no label'}; cites {', '.join(h['cites']) or 'nothing'}]  {att}")
    print(f"\nroot {d['root']}" + (f"  (paper {d['paper']})" if d["paper"] else ""))
    for line in d["notes"] + d["messages"]:
        print(line, file=sys.stderr)
    return 1 if not d["ok"] or (args.strict and d["stale"]) else 0


def cmd_why(L, args):
    n = args.claim
    if n not in L.claims:
        raise LedgerError(f"unknown claim {n}")
    w = L.why_data(n)
    tools = "".join(f", {name} {word}" for name, word in w["tools"].items())
    print(f"{n} [{w['source']}]: {w['statement']}\n  evidence {w['evidence']}{tools}, spec {w['spec'][:12]}")
    print("  rests on:")
    for r in w["rests_on"]:
        print(f"    {r['provenance']:9} {r['id']}")
    if w["recorded"]:
        print("  provenance (recorded in the root, not part of what an attestation binds to):")
        for r in w["recorded"]:
            print(f"    {r['provenance']:9} {r['id']}")
    print("  register:", ", ".join(w["register"]) or "(empty)")
    for m, ds in sorted(w["step_of"].items()):
        print(f"  step of {m}: its proofs use {', '.join(ds)}")
    for lab, others in w["shares_label"].items():
        print(f"  shares the label {lab} with {', '.join(others)}")
    for a in w["attestations"]:
        print(f"  attested {a['level']} by {a['person']} on {a['date']}: "
              f"{'current' if a['current'] else 'STALE (its statement or the evidence it binds to changed since)'}")
    return 0


TEX_SPECIAL = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_",
               "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}


def tex_esc(x):
    """Plain text (claim texts, names) as text-mode TeX; Unicode math symbols as in Lean blocks."""
    return "".join(uni_tex(ch) for ch in str(x))


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
              f"\\def\\LedgerFormat{{{FORMAT_VERSION}}}", f"\\def\\LedgerDate{{{datetime.date.today().isoformat()}}}",
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
    tools = L.tools_in_scope()
    worst = dict(conditional=0, open=0, failed=0)  # claims by their worst machine-check status
    for n in names:
        cnt[L.attestation_summary(n)] += 1
        sts = [L.adapter_state(t, n)[0] for t in tools]
        sts = ["failed" if x == "missing" else x for x in sts if x != "none"]
        if sts and max(sts, key=ADAPTER_STATUS.index) in worst:
            worst[max(sts, key=ADAPTER_STATUS.index)] += 1
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
        st = L.attestation_state(n)
        cells = ""
        for t in tools:  # one neutral cell per tool: the adapter's text for its worst word
            status, word = L.adapter_state(t, n)
            text = tex_esc(L.adapters[t]["labels"].get(word, word))
            if status == "conditional":
                hs = sorted(L.claim_hypotheses(n), key=lambda h: hkey[h])
                text += " [" + ", ".join(hkey[h] for h in hs) + "]" if hs else " hyp."
            cells += f"&\\LedgerToolCell{{{status}}}{{{text}}}"
        att = ("\\LedgerAtts{" + "\\\\[2pt]".join(
            f"\\LedgerAtt{{{lvl}}}{{{tex_esc(p)}}}{{{tex_esc(date)}}}{{{'current' if cur else 'stale'}}}{{{L.signature_of(n, p)}}}"
            for p, lvl, date, cur in st) + "}") if st else "\\LedgerNoAtt"
        ref = reference(c, lab)
        res = (f"{ref} {{\\scriptsize\\texttt{{{tex_esc(lab)}}}}}" if ref else f"\\texttt{{{tex_esc(lab)}}}") \
            + (f" {{\\scriptsize({tex_esc(n)})}}" if seen[lab] > 1 and lab != n else "")
        rows.append(f"\\LedgerRow{{{res}}}{{{tex_esc(L.ev(c))}}}{{{L.stmt[n][1]}}}"
                    f"{{{cells}}}{{{len(L.register[n])}}}{{{att}}}")
    counted = [(n, p, "claim") for n in names for p, *_ in L.attestation_state(n)]
    counted += [(h, p, "hypothesis") for h in L.scope_hyps for p, *_ in L.hypothesis_state(h)]
    nsigned = sum(L.signature_of(n, p, t) == "signed" for n, p, t in counted)
    keyrows = []
    for i, q in sorted(L.payload.items()):
        if q["kind"] == "key":
            kc = q["content"]
            keyrows.append(f"\\LedgerKeyRow{{{tex_esc(kc['person'])}}}{{{tex_esc(fingerprint(kc['public']))}}}"
                           f"{{{tex_esc(kc.get('source') or 'paper')}}}{{{'revoked ' + tex_esc(kc['revoked']) if kc.get('revoked') else ''}}}%")
    allparsed_h = [x for v in L.parsed.values() for x in v]
    hrows = []
    for h in sorted(L.scope_hyps, key=lambda h: hkey[h]):
        meta = L.hypotheses.get(h, {})
        lab = meta.get("label")
        ref = (reference_tex(lab, [x for v in L.parsed.values() for x in v], L.kind_words) if lab else None) or "---"
        hst = L.hypothesis_state(h)
        att = ("\\LedgerAtts{" + "\\\\[2pt]".join(
            f"\\LedgerAtt{{{lvl}}}{{{tex_esc(p)}}}{{{tex_esc(date)}}}{{{'current' if cur else 'stale'}}}"
            f"{{{L.signature_of(h, p, 'hypothesis')}}}"
            for p, lvl, date, cur in hst) + "}") if hst else "\\LedgerNoAtt"
        hrows.append(f"\\LedgerHypRow{{{hkey[h]}}}{{{ref}}}{{\\texttt{{{tex_esc(h)}}}}}{{{tex_esc(', '.join(meta.get('cites', [])) or '---')}}}{{{att}}}%")
    nknown = sum(L.known_theorem(h) for h in L.scope_hyps)
    # for \\ledgersummary, a paragraph in the paper's own text: counts and ready-made prose lists
    checked, notool, by_tool = 0, 0, {t: 0 for t in tools}
    for n in names:
        sts = {t: L.adapter_state(t, n)[0] for t in tools}
        sts = {t: x for t, x in sts.items() if x != "none"}
        for t, x in sts.items():
            by_tool[t] += x in ("ok", "conditional")
        notool += not sts
        checked += bool(sts) and all(x in ("ok", "conditional") for x in sts.values())
    used = [(tex_esc(L.adapters[t]["title"]), k) for t, k in by_tool.items() if k]
    # neutral: which tool checks how many results; what a check is worth is the evidence type's business
    tool_counts = (f"{used[0][0]} for all of them" if len(used) == 1 and used[0][1] == len(names)
                   else ", ".join(f"{t} for {k}" for t, k in used))
    ev_of = [L.ev(L.claims[n]) for n in names]
    ev_counts = ", ".join(f"{tex_esc(e['name'])}: {ev_of.count(e['id'])}" for e in L.evidence if e["id"] in ev_of)
    attesters = sorted({p for n in names for p, _, _, cur in L.attestation_state(n) if cur})
    nattested = sum(any(cur for *_, cur in L.attestation_state(n)) for n in names)
    levels = ", ".join(f"{cnt[k]} {k}" for k in LEVELS if cnt[k])
    hyp_refs = prose_list([reference_tex(L.hypotheses.get(h, {}).get("label"), allparsed_h, L.kind_words)
                           if L.hypotheses.get(h, {}).get("label") else f"\\texttt{{{tex_esc(h)}}}"
                           for h in sorted(L.scope_hyps, key=lambda h: hkey[h])])
    hyp_attesters = sorted({p for h in L.scope_hyps for p, lvl, _, cur in L.hypothesis_state(h) if cur and lvl == "green"})
    allparsed = allparsed_h
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
          f"\\def\\LedgerNSplit{{{len(L.split_labels())}}}",
          "\\def\\LedgerSplit{%s}" % "; ".join(
              f"{reference_tex(lab, allparsed, L.kind_words) or tex_esc(lab)} ({', '.join(tex_esc(x) for x in ns)})"
              for lab, ns in sorted(L.split_labels().items(), key=lambda t: unc_pos(t[0]))),
          "\\def\\LedgerUncovered{%s}" % ", ".join(uncovered_refs),
          "\\def\\LedgerUncoveredRefs{%s}" % prose_list(
              [reference_tex(lab, allparsed, L.kind_words) or f"\\texttt{{{tex_esc(lab)}}}" for lab in sorted(L.uncovered(), key=unc_pos)]),
          f"\\def\\LedgerNChecked{{{checked}}}", f"\\def\\LedgerNNoTool{{{notool}}}",
          "\\def\\LedgerToolCounts{%s}" % tool_counts,
          "\\def\\LedgerEvidenceCounts{%s}" % ev_counts,
          f"\\def\\LedgerNAttested{{{nattested}}}",
          "\\def\\LedgerAttesters{%s}" % prose_list([tex_esc(p) for p in attesters]),
          "\\def\\LedgerAttLevels{%s}" % levels,
          "\\def\\LedgerHypRefs{%s}" % hyp_refs,
          "\\def\\LedgerHypAttesters{%s}" % prose_list([tex_esc(p) for p in hyp_attesters]),
          "\\def\\LedgerKeys{%"] + keyrows + ["}"]
    cl += [f"\\def\\LedgerN{k}{{{v}}}" for k, v in (("Green", cnt["green"]), ("Yellow", cnt["yellow"]),
           ("Conj", cnt["conjecture"]), ("Stale", cnt["stale"]), ("None", cnt["none"]),
           ("Conditional", worst["conditional"]), ("Open", worst["open"]), ("Failed", worst["failed"]))]
    # the tool columns, and the legends: all from the configuration and the adapters, nothing tool-specific here
    titles = [tex_esc(L.adapters[t]["title"]) for t in tools]
    tool_w = 2.6
    cl += ["\\def\\LedgerToolCols{%s}" % ("l" * len(tools)), "\\def\\LedgerToolHead{%s}" % "".join("& " + x for x in titles),
           f"\\def\\LedgerToolWidth{{{tool_w}cm}}", f"\\def\\LedgerResultWidth{{{max(4.0, 10.2 - tool_w * len(tools)):.1f}cm}}",
           "\\def\\LedgerToolNames{%s}" % (", ".join(titles) or "none"),
           "\\def\\LedgerToolLegend{%s}" % " ".join(f"{titles[k]}: {tex_esc(L.adapters[t]['legend'])}"
                                                    for k, t in enumerate(tools) if L.adapters[t]["legend"]),
           "\\def\\LedgerEvidenceLegend{%s}" % ", ".join(f"{tex_esc(e['id'])} {tex_esc(e['name'])}" for e in L.evidence),
           f"\\def\\LedgerNChecklist{{{len(L.checklist)}}}",
           "\\def\\LedgerChecklist{%s}" % "; ".join(f"{tex_esc(k)}: {tex_esc(v['text'])}" for k, v in L.checklist.items())]
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


def review_relations_tex(L, n, names):
    """Relations of claim n to other claims, and a framed list of everything n rests on beyond kernel-checked Lean:
    its register (assertions, hypotheses, cited results, axioms, sorry, models; inherited ones with the claim they
    come from) and other evidence files."""
    tt = lambda x: "\\texttt{" + tex_esc(x) + "}"
    c = L.claims[n]
    rel = []
    for lab, ns in L.split_labels().items():
        if n in ns:
            rel.append(f"\\textbf{{shares the label}} {tt(lab)} with " + ", ".join(tt(x) for x in ns if x != n))
    steps = sorted(L.used_in(n).items())
    if steps:
        rel.append("\\textbf{step of} " + ", ".join(f"{tt(m)} ({', '.join(tex_esc(d.split('.')[-1]) for d in ds)})"
                                                  for m, ds in steps))
    if c.get("uses"):
        rel.append("\\textbf{uses} " + ", ".join(tt(u) for u in c["uses"]))
    users = [m for m in L.claims if n in L.claims[m].get("uses", [])]
    if users:
        rel.append("\\textbf{used by} " + ", ".join(tt(m) for m in users))
    out = ["{\\small \\textbf{Relations:} " + "; ".join(rel) + ".}\\par\\medskip"] if rel else []
    items = []
    for r in L.register.get(n, []):
        kind, _, name = r.partition(":")
        origin = L.register_origin(n, r)
        via = "" if origin in (None, n) else f" \\emph{{(from {tt(origin)}, through \\texttt{{uses}})}}"
        if kind == "assertion":
            a = L.assertions.get(name, {})
            items.append(f"\\textbf{{Assertion}} {tt(name)}{via}: {tex_esc(a.get('text', ''))}")
        elif kind == "hyp" and name.startswith("cited:"):
            items.append(f"\\textbf{{Cited result}} {tt(name[6:])}{via}, taken from the literature")
        elif kind == "hyp":
            known = "attested as a known theorem" if L.known_theorem(name) else "not attested as a known theorem"
            items.append(f"\\textbf{{Hypothesis}} {tt(name)}{via} of the Lean statement, {known}")
        elif kind == "axiom":
            items.append(f"\\textbf{{Axiom}} {tt(name)}{via}")
        elif kind == "sorry":
            items.append(f"\\textbf{{Unproved (sorry)}} {tt(name)}{via}")
        elif kind == "model":
            items.append(f"\\textbf{{ProVerif model}} {tt(name)}{via}: faithfulness to the protocol is not checked")
        elif kind == "evidence":
            items.append(f"\\textbf{{No checked evidence}}{via}: no Lean, adapter or file evidence")
        else:
            items.append(tt(r) + via)
    files = c.get("files", [])
    if items or files:
        body = ""
        if items:
            body += ("\\textbf{Rests on, beyond kernel-checked Lean:}\\begin{itemize}\\itemsep0pt\\topsep2pt"
                     + "".join("\\item " + x for x in items) + "\\end{itemize}")
        if files:
            body += "\\textbf{Other evidence (not checked by the ledger):} " + ", ".join(tt(f) for f in files) + "."
        out.append("\\noindent\\fbox{\\parbox{\\dimexpr\\linewidth-2\\fboxsep-2\\fboxrule\\relax}{\\small " + body + "}}\\par\\medskip")
    elif c.get("lean"):
        out.append("{\\small \\textbf{Rests on:} kernel-checked Lean only, standard axioms.}\\par\\medskip")
    return out


LEAN_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
                       r"(def|abbrev|structure|class|inductive|instance|theorem|lemma|opaque|axiom)\s+([^\s:({\[]+)")
LEAN_PREAMBLE = ("namespace ", "open ", "variable ", "section", "set_option ", "universe ")


def split_extract(text):
    """A statement extract as (preamble lines, [(kind, name, block)]): header comment, imports and `end` lines
    removed; a docstring belongs to the declaration after it; a block runs to the next top-level line."""
    text = re.sub(r"\A\s*/-(?!-).*?-/\s*", "", text, count=1, flags=re.S)
    pre, decls, cur, doc, in_doc = [], [], None, [], False
    for line in text.splitlines():
        if in_doc or line.startswith("/--"):
            doc.append(line)
            in_doc = "-/" not in line  # a docstring may span lines
            continue
        m = LEAN_DECL.match(line)
        if m:
            cur = [m.group(1), m.group(2), doc + [line]]
            decls.append(cur)
            doc = []
        elif line.startswith(LEAN_PREAMBLE):
            pre.append(line); cur = None
        elif line.startswith("import ") or re.match(r"^end(\s|$)", line):
            cur = None
        elif cur is not None:
            cur[2].append(line)
    return pre, [(k, n, "\n".join(b).strip("\n")) for k, n, b in decls]


DEF_KINDS = {"def", "abbrev", "structure", "class", "inductive", "instance", "opaque", "axiom"}


def review_definitions(L, names, extract_of):
    """The definitions of all extracts, each once: (LaTeX section, {claim: [(number, name)]}, {claim: theorem text})."""
    pre, defs, uses, thms = [], {}, {}, {}  # defs: name -> [[text, [claims]]] in order of first appearance
    for n in names:
        f = extract_of(n)
        if not (f and f.is_file()):
            continue
        p, ds = split_extract(f.read_text(errors="replace"))
        pre += [x for x in p if x not in pre]
        uses[n], body = [], []
        for kind, name, block in ds:
            if kind not in DEF_KINDS:
                body.append(block)
                continue
            variants = defs.setdefault(name, [])
            for v in variants:
                if v[0] == block:
                    v[1].append(n); break
            else:
                variants.append([block, [n]])
            uses[n].append((name, next(k for k, v in enumerate(variants) if v[0] == block)))
        thms[n] = "\n\n".join(body)
    number = {name: k + 1 for k, name in enumerate(defs)}
    out = ["\\clearpage\\onecolumn{\\Large\\bfseries Definitions}\\phantomsection\\label{rv:defs}\\par\\smallskip",
           "Every Lean definition that a claim's statement rests on, once, in the order in which they first occur. "
           "Each claim lists the numbers of the definitions it uses. A definition shown in several variants appears in "
           "different texts in the extracts of different claims; the claims are named.\\par\\medskip"]
    if pre:
        out.append(lean_to_tex("\n".join(pre)) + "\\par\\medskip")
    for name, variants in defs.items():
        for k, (block, users) in enumerate(variants):
            tag = f"D{number[name]}" + (chr(ord("a") + k) if len(variants) > 1 else "")
            who = f" {{\\small(variant used by {', '.join(tex_esc(u) for u in users)})}}" if len(variants) > 1 else ""
            back = ", ".join(f"\\rvlink{{rv:{u}}}{{\\texttt{{{tex_esc(u)}}}}}" for u in users) if len(users) <= 8 \
                else f"{len(users)} claims"
            out.append(f"\\noindent\\textbf{{{tag}}} \\texttt{{{tex_esc(name)}}}{who}\\phantomsection\\label{{rv:def:{tag}}}"
                       f"\\hfill{{\\footnotesize used by {back}}}\\par")
            out.append(lean_to_tex(block) + "\\par\\smallskip")
    refs = {n: [(f"D{number[name]}" + (chr(ord("a") + k) if len(defs[name]) > 1 else ""), name) for name, k in u]
            for n, u in uses.items()}
    return out, refs, thms


def definition_refs(refs):
    """'D1–D18, D20 rhoP (p. 4), ...': consecutive numbers of three or more as a range, the others by name and page."""
    key = lambda t: (int(re.match(r"D(\d+)", t[0]).group(1)), t[0])
    refs = sorted(set(refs), key=key)
    out, k = [], 0
    while k < len(refs):
        j = k
        while j + 1 < len(refs) and refs[j][0][1:].isdigit() and refs[j + 1][0] == f"D{int(refs[j][0][1:]) + 1}":
            j += 1  # variants (D7a, D7b) are never part of a range
        link = lambda t: f"\\rvlink{{rv:def:{t}}}{{{t}}}"
        if j - k >= 2:
            out.append(f"{link(refs[k][0])}--{link(refs[j][0])}")
        else:
            out += [f"{link(t)}~\\texttt{{{tex_esc(name.split('.')[-1])}}} (p.~\\rvlink{{rv:def:{t}}}{{\\pageref{{rv:def:{t}}}}})" for t, name in refs[k:j + 1]]
        k = j + 1
    return ", ".join(out)


READING_HEAD = re.compile(r"\\(paragraph|subparagraph)\{")
READING_STMT = re.compile(r"translation|theorem|lemma|proposition|corollary|statement|conclusion|claim|result|hypothes|"
                          r"assumption", re.I)
READING_OTHER = re.compile(r"plain-language|setting|notation|object|definition|point|caveat|unexpected|reader|remark|"
                           r"convention|interpretation", re.I)


def brace_end(s, i):
    """Index of the brace closing the one at s[i]."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return j
    return len(s) - 1


def reading_headings(tex):
    r"""Headings of a back-translation (pandoc writes # as \paragraph, ## as \subparagraph):
    [(start, end of heading, level, plain title)]."""
    out = []
    for m in READING_HEAD.finditer(tex):
        e = brace_end(tex, m.end() - 1)
        title = tex[m.end():e]
        t = re.match(r"\\texorpdfstring\{", title)
        if t:  # the second argument is the plain text
            a = brace_end(title, t.end() - 1)
            title = title[a + 2:brace_end(title, a + 1)]
        out.append((m.start(), e + 1, 0 if m.group(1) == "paragraph" else 1,
                    " ".join(re.sub(r"\\[a-zA-Z]+|[{}]", "", title).split())))
    return out


def reading_statement(tex):
    """The part of a back-translation that states the theorem(s), for the comparison with the paper: the sections
    whose heading names a theorem, statement, hypotheses or conclusion, not the setting, notation or caveats. A heading
    with sub-sections counts only through them, or, if none of them qualifies, through its own lead text.
    Returns (LaTeX, [section titles]); ("", []) if no section qualifies (the reading has no fixed structure)."""
    hs, parts = reading_headings(tex), []
    stmt = lambda t: READING_STMT.search(t) and not READING_OTHER.search(t)
    for k, (s, e, lvl, title) in enumerate(hs):
        if parts and parts[-1][1] > s:
            continue
        end = next((h[0] for h in hs[k + 1:] if h[2] <= lvl), len(tex))
        kids = [h for h in hs[k + 1:] if h[0] < end]
        if not kids:
            if stmt(title):
                parts.append((s, end, title))
        elif not any(stmt(h[3]) for h in kids) and READING_STMT.search(title) and len(tex[e:kids[0][0]].strip()) > 200:
            parts.append((s, kids[0][0], title))
    return "\n".join(tex[s:e] for s, e, _ in parts), [t for *_, t in parts]


def strip_labels(tex):
    return re.sub(r"\\label\{[^}]*\}", "", tex)


REF = re.compile(r"\\(?:eq|c|C|auto|page)?ref\{([^}]*)\}")


def paper_proof_refs(L, lab):
    """Labels the paper's proof of the result `lab` refers to: the proof environment whose optional argument names
    `lab` ("Proof of Theorem~\ref{lab}"), else the first proof after the statement, before the next statement.
    Reading aids (`[review] skip_envs`) are left out. [] if the result has no proof in the paper."""
    text = strip_comments(L.flat.get(L.paper, ""))
    for env in L.cfg.get("review", {}).get("skip_envs", []):
        text = re.sub(r"\\begin\{" + re.escape(env) + r"\}.*?\\end\{" + re.escape(env) + r"\}", "", text, flags=re.S)
    m = re.search(r"\\label\{" + re.escape(lab) + r"\}", text)
    if not m:
        return []
    proof = None
    for p in re.finditer(r"\\begin\{proof\}(\[[^\n]*?\])?", text):
        if p.group(1) and re.search(r"\{" + re.escape(lab) + r"\}", p.group(1)):
            proof = p; break
    if proof is None:
        nxt = re.compile(r"\\begin\{(" + "|".join(sorted(STATEMENT_ENVS | RESULT_ENVS)) + r")\*?\}")
        after = text[m.end():]
        p, q = re.search(r"\\begin\{proof\}(\[[^\n]*?\])?", after), nxt.search(after)
        if not p or (q and q.start() < p.start()) or (p.group(1) and REF.search(p.group(1))):
            return []
        proof = p
        start = m.end() + p.end()
    else:
        start = proof.end()
    end = text.find("\\end{proof}", start)
    body = text[start:end if end >= 0 else len(text)]
    return [x.strip() for g in REF.findall(body) for x in g.split(",") if x.strip() and x.strip() != lab]


def review_scope(L, targets):
    """Claims to review for the given labels or claim names: those claims and everything they rest on, through
    `uses`, through the Lean proofs (the claims they have as steps) and through the paper's proofs (the results
    and equations a proof refers to), transitively."""
    owner = {lab: n for n, c in L.claims.items() for lab in claim_labels(c)}
    seeds = set()
    for t in targets:
        hit = {n for n, c in L.claims.items() if t == n or t in claim_labels(c)}
        if not hit:
            sys.exit(f"review --for: {t} is neither a claim nor a label of a claim")
        seeds |= hit
    steps = {}  # claim -> the claims that are steps of it
    for n in L.claims:
        for m in L.used_in(n):
            steps.setdefault(m, set()).add(n)
    todo, seen = list(seeds), set()
    while todo:
        n = todo.pop()
        if n not in seen:
            seen.add(n)
            todo += [u for u in L.claims[n].get("uses", []) if u in L.claims] + sorted(steps.get(n, ()))
            todo += [owner[r] for lab in claim_labels(L.claims[n]) for r in paper_proof_refs(L, lab) if r in owner]
    return seen, seeds


def claim_labels(c):
    return c.get("labels") or ([c["label"]] if c.get("label") else [])


def labels_in_paper_order(L, c):
    flat = L.flat.get(c.get("paper"), "")
    pos = lambda lab: (m.start() if (m := re.search(r"\\label\{" + re.escape(lab) + r"\}", flat)) else 10 ** 9)
    return sorted(claim_labels(c), key=pos)


STATUS_WORDS = {"green": "GREEN", "yellow": "YELLOW", "conjecture": "CONJECTURE", "stale": "STALE", "none": "--"}


def review_toc(L, names, seeds, parsed, only):
    """Contents of the packet: one row per paper label, in the order of the paper, with the claim carrying it,
    its Lean declarations and its attestation; result labels the ledger does not cover are listed too."""
    flat = L.flat.get(L.paper, "")
    pos = lambda lab: (m.start() if (m := re.search(r"\\label\{" + re.escape(lab) + r"\}", flat)) else 10 ** 9)
    rows = [(pos(lab), lab, n) for n in names for lab in claim_labels(L.claims[n])]
    rows += [(10 ** 9, None, n) for n in names if not claim_labels(L.claims[n])]
    if rows:
        lo, hi = min(r[0] for r in rows), max(r[0] for r in rows if r[0] < 10 ** 9) if any(r[0] < 10 ** 9 for r in rows) else 0
        for lab in L.uncovered():
            if only is None or lo <= pos(lab) <= hi:
                rows.append((pos(lab), lab, None))
    rows.sort(key=lambda r: (r[0], r[2] or ""))
    w = r"\noindent\makebox[2.7cm][l]{%s}\makebox[3.4cm][l]{%s}\makebox[3.1cm][l]{%s}\makebox[2.1cm][l]{%s}\makebox[0.9cm][r]{%s}\hspace{0.3cm}\parbox[t]{\dimexpr\linewidth-12.5cm\relax}{\raggedright %s}\par"
    out = [r"\medskip{\large\bfseries Contents}\par\smallskip",
           r"{\small One row per labelled result in the order of the paper. Claim and page link to the claim's pages;"
           r" status is the strongest current attestation (" + ("\\textbf{bold}: a claim asked for with \\texttt{--for}; the others are what it rests on; "
                                                              if seeds else "") + r"STALE: only attestations of an earlier statement).}\par\smallskip",
           r"{\footnotesize", w % (r"\textbf{Paper}", r"\textbf{Label}", r"\textbf{Claim}", r"\textbf{Status}", r"\textbf{p.}", r"\textbf{Lean}"),
           r"\vspace{2pt}\hrule\vspace{3pt}"]
    for _, lab, n in rows:
        ref = (reference_tex(lab, parsed, L.kind_words) or "") if lab else "(no label)"
        if n is None:
            out.append(w % (ref, r"\texttt{" + tex_esc(lab) + "}", r"\textit{not in the ledger}", "", "", ""))
            continue
        c = L.claims[n]
        name = r"\texttt{" + tex_esc(n) + "}"
        name = r"\textbf{" + name + "}" if n in seeds else name
        lean = ", ".join(tex_esc(d.split(".")[-1]) for d in c.get("lean", [])) or ("--" if not c.get("lean") else "")
        if not c.get("lean"):
            lean = r"\textit{no Lean}"
        out.append(w % (ref, r"\texttt{" + tex_esc(lab or "") + "}", r"\rvlink{rv:%s}{%s}" % (n, name),
                        STATUS_WORDS.get(L.attestation_summary(n), "?"), r"\rvlink{rv:%s}{\pageref{rv:%s}}" % (n, n), lean))
    out.append("}")
    return out


REVIEW_PREAMBLE = r"""\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\newlength{\lttw}
\providecommand{\rvlink}[2]{\ifcsname hyperref\endcsname\hyperref[#1]{#2}\else #2\fi}
\providecommand{\phantomsection}{}
\ifcsname NoHyper\endcsname\else\newenvironment{NoHyper}{}{}\fi % the paper's citations: no links to a bibliography the packet lacks
% The paper's own labels carry anchors of the paper's PDF, which this packet does not have: their references are
% plain text here, and every link of the packet is an explicit \rvlink to a label of the packet.
\makeatletter
\ifcsname @refstar\endcsname\def\ref{\@ifstar\@refstar\@refstar}\fi
\ifcsname @pagerefstar\endcsname\def\pageref{\@ifstar\@pagerefstar\@pagerefstar}\fi
\makeatother
\definecolor{rvpaper}{RGB}{31,94,165}\definecolor{rvread}{RGB}{176,112,0}\definecolor{rvlean}{RGB}{90,90,90}
\newtcolorbox{rvbox}[2]{breakable,enhanced jigsaw,colback=#1!4!white,colframe=#1,boxrule=0.6pt,arc=1pt,left=5pt,right=5pt,
  top=3pt,bottom=3pt,fonttitle=\small\bfseries,coltitle=black,colbacktitle=#1!18!white,title={#2}}
\gdef\rvhead{}
\makeatletter
\def\ps@rvpage{\def\@oddhead{\footnotesize\rvhead\hfil\thepage}\let\@evenhead\@oddhead
  \def\@oddfoot{}\let\@evenfoot\@oddfoot}
\makeatother
\onecolumn
\setlength{\parindent}{0pt}\setlength{\parskip}{4pt}
\pagestyle{rvpage}"""


def review_body(L, only=None, with_lean=True, defs_once=True, seeds=()):
    """LaTeX body of the review packet of the selected paper. Contents (one row per label), then for each claim a
    comparison page (the paper's statement, the statement part of the model's back-translation, the Lean theorem)
    and its details (relations, what it rests on, the whole back-translation, the assessment); the Lean definitions
    once, in a section of their own. `seeds`: the claims asked for (shown in bold in the contents)."""
    rv = L.cfg.get("review", {})
    parsed = L.parsed.get(L.paper) or [x for v in L.parsed.values() for x in v]
    names = [n for n in L.claims if not only or n in only]
    names.sort(key=lambda n: (L.label_position(L.claims[n]) or (1, 0), n))
    out = [REVIEW_PREAMBLE]
    out.append(r"{\Large\bfseries Review packet for the claims of the paper ``%s''}\par\medskip" % tex_esc(L.paper))
    out.append(r"Ledger root of the paper (this packet is not part of it): \texttt{%s}.\par" % L.root_hash[:32])
    out.append(r"""\medskip\textbf{How to use.} Each claim starts on a new page with the \emph{comparison}: three boxes,
\textcolor{rvpaper}{\textbf{Paper}} (the statement as typeset in the paper, with its number and page; page numbers refer to the
plain build of the paper made for this packet), \textcolor{rvread}{\textbf{Back-translation}} (the part of a model's reading of
the Lean statement that states the theorem; the model saw the Lean text alone) and \textcolor{rvlean}{\textbf{Lean}} (the
theorem as stated, with links to the definitions it uses). The \emph{details} follow: relations to other claims, a framed list
of everything the claim rests on beyond kernel-checked Lean (assertions, hypotheses, cited results, scripts; attesting a claim
covers its statement, not these items), the whole back-translation with its setting and caveats, and a model's
\emph{assessment}. Back-translation and assessment are generated aids and can share a model's blind spots; neither is an
attestation. To attest after reading: \texttt{ledger.py -P %s attest CLAIM --person NAME --level yellow|green --reason ...}.\par
\medskip\textbf{Verdicts of the assessments.} CONSISTENT: no difference found between paper, back-translation and Lean text.
PARTIAL: faithful where it formalises, but this claim covers only part of what the paper states under its label. CHECK: something
specific to look at, see the notes. MISMATCH: a difference that probably needs a fix in the text or in the formalisation.
UNCLEAR: could not be decided.\par""" % tex_esc(L.paper))
    out += review_toc(L, names, set(seeds), parsed, only)
    extract_of = lambda n: L.review_file("extracts", n)
    defrefs = thms = None
    defs_section = []
    if with_lean and defs_once:
        defs_section, defrefs, thms = review_definitions(L, names, extract_of)
    for n in names:
        c = L.claims[n]
        labels = labels_in_paper_order(L, c)
        refs = [reference_tex(lab, parsed, L.kind_words) or tex_esc(lab) for lab in labels]
        where = [f"{r} (p.~\\pageref{{{lab}}})" for r, lab in zip(refs, labels)]
        att = L.attestation_state(n)
        atts = "; ".join(f"{lvl.upper()} by {tex_esc(p)}" + ("" if cur else " (stale)") for p, lvl, _, cur in att) or "not yet attested"
        head = f"Claim \\texttt{{{tex_esc(n)}}}" + (" \\textperiodcentered{} " + ", ".join(refs) if refs else "")
        out.append("\\clearpage\\onecolumn")  # again: a page break inside one-column mode can fall back to two columns (ltxgrid classes)
        out.append(f"\\gdef\\rvhead{{{head}}}")
        out.append(f"{{\\Large\\bfseries Claim \\texttt{{{tex_esc(n)}}}}}\\phantomsection\\label{{rv:{n}}}\\par\\smallskip")
        out.append(f"{{\\small \\textbf{{In the paper:}} {'; '.join(where) or 'no label (ledger text only)'}.\\quad "
                   f"\\textbf{{Evidence}} {tex_esc(L.ev(c))}; \\textbf{{Lean}}: {lean_status_words(L, n)}; "
                   f"\\textbf{{attestation}}: {atts}.}}\\par\\medskip")
        # -- comparison
        seen = set()
        paper = "\n".join(review_statement_tex(L, lab, parsed, seen) for lab in labels) if labels else \
            "\\noindent\\textit{No label in the paper; text recorded in the ledger:} " + tex_esc(L.stmt[n][0])
        out.append("\\begin{rvbox}{rvpaper}{Paper: " + (", ".join(where) or "ledger text") + "}\n\\begin{NoHyper}" + paper
                   + "\\end{NoHyper}\n\\end{rvbox}")
        rd = L.review_file("readings", n)
        reading = strip_labels(rd.read_text(errors="replace")) if rd and rd.is_file() else ""
        part, titles = reading_statement(reading) if reading else ("", [])
        if not reading:
            out.append("\\begin{rvbox}{rvread}{Back-translation}\n\\noindent\\textit{No back-translation file for this claim.}\n\\end{rvbox}")
        elif part:
            out.append("\\begin{rvbox}{rvread}{Back-translation, statement part (" + str(len(titles)) + " section"
                       + ("s" if len(titles) > 1 else "") + f"; the whole reading is on p.~\\rvlink{{rv:{n}:reading}}{{\\pageref{{rv:{n}:reading}}}})}}\n"
                       + part + "\n\\end{rvbox}")
        else:
            out.append("\\begin{rvbox}{rvread}{Back-translation, in full (no section of it is recognisable as the statement)}\n"
                       + reading + "\n\\end{rvbox}")
        ex = extract_of(n)
        if with_lean and defrefs is not None and n in thms:
            used = definition_refs(defrefs[n])
            out.append("\\begin{rvbox}{rvlean}{Lean statement (definitions: section Definitions, p.~\\rvlink{rv:defs}{\\pageref{rv:defs}})}\n"
                       + lean_to_tex(thms[n].strip("\n")) + "\\par\\smallskip\n{\\small\\textbf{Uses the definitions} "
                       + (used or "none") + ".}\n\\end{rvbox}")
        elif with_lean and ex and ex.is_file():
            text = ex.read_text(errors="replace")
            text = re.sub(r"\A\s*/-.*?-/\s*", "", text, count=1, flags=re.S) if text.lstrip().startswith("/-") else text
            text = re.sub(r"(?m)^import .*\n", "", text)
            out.append("\\begin{rvbox}{rvlean}{Lean statement (source extract: definitions, then the statement)}\n"
                       + lean_to_tex(text.strip("\n")) + "\n\\end{rvbox}")
        # -- details
        out.append("\\medskip{\\large\\bfseries Details}\\par\\smallskip")
        out += review_relations_tex(L, n, names)
        if part:
            out.append(f"{{\\bfseries Back-translation, whole}}\\phantomsection\\label{{rv:{n}:reading}} {{\\small(generated by a model from the Lean text alone)}}\\par\\smallskip")
            out.append(reading + "\\par\\medskip")
        a = L.assessments.get(n)
        out.append("{\\bfseries Assessment} {\\small(generated by a model; an aid for the reviewer, not an attestation)}\\par\\smallskip")
        if a:
            ast = L.assessment_state(n)
            note = {"outdated": "OUTDATED: " + "; ".join(ast["why"]) + ". Read the verdict as describing an older state.",
                    "unbound": "not bound to a statement: it does not record what it judged, so it may be out of date"}.get(ast["state"])
            out.append(f"\\noindent\\textbf{{{VERDICT_TEXT.get(a.get('verdict'), a.get('verdict', '?'))}}} "
                       f"{{\\small({tex_esc(a.get('model', '?'))}, {tex_esc(a.get('date', ''))})}}\\par\n"
                       + (f"\\noindent{{\\small\\bfseries {tex_esc(note)}}}\\par\\smallskip\n" if note else "")
                       + a.get('notes', ''))
        else:
            out.append("\\noindent\\textit{No assessment yet.}")
    if defs_section:
        out.append("\\gdef\\rvhead{Definitions}")
        out += defs_section
    if L.scope_hyps:
        out.append("\\clearpage\\onecolumn\\gdef\\rvhead{Hypotheses}{\\Large\\bfseries Hypotheses}\\par\\smallskip")
        for h in L.scope_hyps:
            meta = L.hypotheses.get(h, {})
            out.append(f"\\noindent\\textbf{{\\texttt{{{tex_esc(h)}}}}}\\quad cites: {tex_esc(', '.join(meta.get('cites', [])) or 'nothing')}.\\par")
            if meta.get("label"):
                out.append("\\begin{NoHyper}" + review_statement_tex(L, meta["label"], parsed, set()) + "\\end{NoHyper}")
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
                rp = L.review_file("readings", n)
                if rp.is_file():
                    shutil.copy(rp, work / "readings" / f"{n}.tex")
        only = set(args.claims.split(",")) if args.claims else None
        seeds = ()
        if getattr(args, "for_", None):
            scope, seeds = review_scope(L, [t.strip() for t in args.for_.split(",") if t.strip()])
            only = scope if only is None else only | scope
        body = review_body(L, only, with_lean=not args.no_lean, defs_once=not args.defs_inline, seeds=seeds)
        (work / "review-body.tex").write_text(body)
        # amsmath/amssymb: the packet uses starred display environments and \\tag, whatever the paper loads
        inject = ("\\AddToHook{begindocument/before}{\\RequirePackage{amsmath,amssymb,tcolorbox}\\tcbuselibrary{breakable,skins}}"
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


def read_lock(f):
    lock = json.loads(Path(f).read_text())
    if lock.get("format") not in READS_FORMATS:
        sys.exit(f"{f}: ledger format {lock.get('format')!r}; this ledger.py ({__version__}) reads format "
                 f"{FORMAT_VERSION} only")
    return lock


def cmd_verify(L, args):
    f = L.lockfile
    if not f.exists():
        sys.exit(f"no {f.name}: run `lock` first")
    old, new, bad = read_lock(f), L.lock(), list(L.errors)
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
    rec = L.make_attestation(args.person, args.level, claim=args.claim, hypothesis=args.hypothesis, reason=args.reason,
                             checklist=[x for x in (args.checklist or "").split(",") if x])
    extra = ""
    if args.sign:
        if not args.key:
            raise LedgerError("--sign needs --key KEYID (a key registered with `addkey`, or --pub for a standalone file)")
        pub = L.sign_attestation(rec, args.key, args.sign, pub=Path(args.pub).read_text().strip() if args.pub else None)
        if args.out:  # a standalone file carries the key it was made with
            extra = toml_record(f"[key.{args.key}]", dict(person=args.person, public=pub, source="attestation-file"))
    out = L.append_attestation(rec, args.out, extra, snapshot=not args.no_snapshot)
    print(f"recorded {args.level} by {args.person} on {args.claim or 'hypothesis ' + args.hypothesis}, bound to {rec['bound'][:12]}"
          + (", signed" if "sig" in rec else "") + (f" -> {out}" if args.out else ""))
    return 0


# ---------------------------------------------------------------- assess: write or bind an assessment
def assessment_blocks(text):
    """{claim name: (first line, line after the last)} of the `[assessment.NAME]` tables of a TOML text. Multi-line strings
    are skipped over, so a line starting with `[` inside `notes` does not end a table."""
    lines, blocks, cur, ml = text.split("\n"), {}, None, None
    for i, ln in enumerate(lines):
        if ml is None and ln.startswith("["):
            if cur:
                blocks[cur[0]] = (cur[1], i)
                cur = None
            m = re.match(r'\[assessment\.(?:"([^"]+)"|([A-Za-z0-9_-]+))\]\s*(#.*)?$', ln)
            if m:
                cur = (m.group(1) or m.group(2), i)
        for d in ("'''", '"""'):
            if ml in (None, d) and ln.count(d) % 2 == 1:
                ml = None if ml == d else d
                break
    if cur:
        blocks[cur[0]] = (cur[1], len(lines))
    return blocks


def toml_multiline(text):
    """A TOML value for text that may contain newlines and backslashes (a LaTeX fragment): a literal string if possible."""
    if "'''" not in text:
        return "'''\n" + text.strip("\n") + "\n'''"
    return json.dumps(text, ensure_ascii=False)


def cmd_assess(L, args):
    """Record an assessment of a claim together with the state it judged, or bind an existing one to the present state."""
    names = args.claims
    for n in names:
        if n not in L.claims:
            raise LedgerError(f"unknown claim {n}")
    if args.audit:
        rows = L.audit_assessments(set(names) or None)
        for r in rows:
            print(f"{r['claim']:24} {r['state']:10} written {r['date'] or '?'}" + (f" (commit {r['commit'][:10]})" if r["commit"] else "")
                  + (f": changed since: {', '.join(r['changes'])}" if r["changes"] else "") + (f"; {r['note']}" if r["note"] else ""))
        n_un = sum(r["state"] == "unchanged" for r in rows)
        print(f"\n{len(rows)} unbound assessment(s): {n_un} unchanged, {sum(r['state'] == 'changed' for r in rows)} changed, "
              f"{sum(r['state'] == 'unknown' for r in rows)} unknown.")
        if args.bind_unchanged and n_un:
            todo = [r["claim"] for r in rows if r["state"] == "unchanged"]
            print(f"binding {len(todo)} unchanged assessment(s) to the present state: {', '.join(todo)}")
            args.claims, args.audit, args.bind = todo, False, True
            return cmd_assess(L, args)
        elif n_un:
            print("`assess --audit --bind-unchanged` binds the unchanged ones (it says that you know they still fit); the changed ones need a new assessment.")
        return 0
    if not names:
        raise LedgerError("give a CLAIM (or --audit)")
    where = {}
    for f in sorted(L.dir.glob("*.toml")):
        for n in assessment_blocks(f.read_text(encoding="utf-8")):
            where[n] = f
    if args.bind:
        if args.verdict or args.notes_file or args.model:
            raise LedgerError("--bind only adds what an existing assessment judged; do not combine it with --verdict/--model/--notes-file")
        for n in names:
            if n not in where:
                raise LedgerError(f"{n} has no assessment to bind")
            f = where[n]
            text = f.read_text(encoding="utf-8")
            a, b = assessment_blocks(text)[n]
            lines = text.split("\n")
            body = [x for x in lines[a + 1:b] if not re.match(r"(spec|reading)\s*=", x)]
            extra = [f"spec = {json.dumps(L.cspec[n])}"] + ([f"reading = {json.dumps(L.reading_hash(n))}"] if L.reading_hash(n) else [])
            f.write_text("\n".join(lines[:a + 1] + extra + body + lines[b:]), encoding="utf-8")
            print(f"bound the assessment of {n} to the present state (spec {L.cspec[n][:12]}): it now counts as current. "
                  f"That says you know it still describes this statement; it was last written {L.assessments[n].get('date', '?')}.")
        return 0
    if len(names) != 1:
        raise LedgerError("give exactly one claim to write an assessment for (or --bind for several)")
    n = names[0]
    if args.verdict not in ASSESSMENT_VERDICTS:
        raise LedgerError(f"--verdict must be one of {', '.join(ASSESSMENT_VERDICTS)}")
    if not args.model:
        raise LedgerError("--model NAME is needed: who or what wrote the assessment")
    if not (args.notes_file or args.notes):
        raise LedgerError("--notes-file FILE (a LaTeX fragment) or --notes TEXT is needed")
    notes = Path(args.notes_file).read_text(encoding="utf-8") if args.notes_file else args.notes
    rec = [f"[assessment.{n}]", f"model = {json.dumps(args.model, ensure_ascii=False)}",
           f"date = {json.dumps(args.date or datetime.date.today().isoformat())}", f"verdict = {json.dumps(args.verdict)}",
           f"spec = {json.dumps(L.cspec[n])}"] + ([f"reading = {json.dumps(L.reading_hash(n))}"] if L.reading_hash(n) else []) \
        + [f"notes = {toml_multiline(notes)}"]
    f = where.get(n) or (L.dir / "assessments.toml")
    text = f.read_text(encoding="utf-8") if f.exists() else ""
    if n in where:
        a, b = assessment_blocks(text)[n]
        lines = text.split("\n")
        tail = lines[b:]
        out = "\n".join(lines[:a] + rec + ([""] if tail and tail[0].strip() else []) + tail)
    else:
        out = text.rstrip("\n") + ("\n\n" if text.strip() else "") + "\n".join(rec) + "\n"
    f.write_text(out, encoding="utf-8")
    print(f"recorded the {args.verdict} assessment of {n} by {args.model}, bound to spec {L.cspec[n][:12]}" +
          (f" and back-translation {L.reading_hash(n)[:12]}" if L.reading_hash(n) else "") +
          f" -> {f.relative_to(L.root)}" + ("" if n not in where else " (replaced the earlier one)"))
    return 0


def cmd_snapshot(L, args):
    """Record snapshots for current attestations that have none (so that `diff` can later show what changed); with
    --from-git, also rebuild those of stale attestations from the project's history."""
    done = L.record_snapshots(dry_run=args.dry_run)
    print(f"{'would record' if args.dry_run else 'recorded'} {len(done)} snapshot(s) of current attestations" + (": " + ", ".join(done) if done else "") +
          "; the others already have one or have no current attestation")
    if args.from_git:
        res = L.recover_snapshots(targets=set(args.targets) or None, depth=args.depth, dry_run=args.dry_run, partial=args.partial)
        for r in res:
            print(f"  {r['kind']} {r['target']} (bound {r['bound'][:12]}): {r['status']}" +
                  (f" from commit {r['commit'][:10]}" if r["commit"] else "") + (f"; {r['note']}" if r["note"] else ""))
        if not res:
            print("no stale attestation without a snapshot in this scope")
    return 0


def cmd_diff(L, args):
    """What changed since the latest attestation of a claim (or hypothesis) that has a snapshot."""
    import difflib
    if bool(args.claim) == bool(args.hypothesis):
        raise LedgerError("give exactly one of CLAIM and --hypothesis NAME")
    d = L.diff_since(claim=args.claim, hypothesis=args.hypothesis)
    name = args.claim or "hypothesis " + args.hypothesis
    if not d["available"]:
        print(f"{name}: {d['reason']}")
        return 0
    a = d["attestation"]
    print(f"{name}: compared with the attestation {a['level']} by {a['person']} on {a['date']} (bound to {a['bound'][:12]})")
    if d["current"]:
        print("  nothing changed: that attestation is current")
        return 0
    if d.get("unverified"):
        print(f"  note: this snapshot was rebuilt from git commit {d['unverified']['commit'][:10]} and is not verified against the attested "
              "hash; only the statement text is compared, not the evidence")
    t = d["text"]
    print("  statement: " + ("changed" if t["changed"] else "unchanged"))
    if t["changed"]:
        for line in difflib.unified_diff(t["old"].splitlines(), t["new"].splitlines(), "attested", "now", lineterm="", n=1):
            print("    " + line)
    g = d.get("git")
    if g:
        print(f"  attested at git commit {g['head'][:10]}" + ("" if not a.get("git_dirty") else " (the tree had uncommitted changes)") +
              (f"; {g['error']}" if g["error"] else f"; files changed since: {len(g['files']) + g['more']}" +
               ("" if not g["files"] else " (" + ", ".join(g["files"][:6]) + (", ..." if len(g["files"]) > 6 else "") + ")")))
    for u in d["uses"]:
        print(f"  uses {u['name']}: {u['change']}")
    for n in d["nodes"]:
        how = "a dependency of it changed" if n["content_same"] else "its statement-level content changed"
        print(f"  {n['kind']:10} {n['id']}: {n['change']}" + (f" ({how})" if n["change"] == "changed" else ""))
    return 0


# ---------------------------------------------------------------- init: bootstrap a new ledger
INIT_SKIP_DIRS = {"ledger", "build", "dist", "out", "site", "node_modules", "__pycache__", "_attic", "venv"}
INIT_CHECKLIST = """\
# What an attesting person can tick; the items they tick are part of what they sign. Edit or delete freely.
[checklist.C1]
text = "compared the statement in the paper with the formal statement or with the check it rests on"
applies = "claim"

[checklist.C2]
text = "re-ran the machine check or the script myself"
applies = "claim"

[checklist.H1]
text = "found the cited source and the statement in it; theorem or page recorded in the citation's source field"
applies = "hypothesis"

[checklist.H2]
text = "compared the cited statement with the formal definition of the hypothesis and with its statement in the paper"
applies = "hypothesis"
"""


def slug(x, fallback="x"):
    """A name that is safe as a bare TOML key and as a command-line argument."""
    return re.sub(r"[^A-Za-z0-9_-]+", "_", str(x)).strip("_") or fallback


def git_user_name():
    try:
        r = subprocess.run(["git", "config", "user.name"], capture_output=True, text=True, timeout=5)
        return r.stdout.strip() if r.returncode == 0 else ""
    except (OSError, subprocess.TimeoutExpired):
        return ""


def find_paper_mains(root, depth=4):
    """Main .tex files below root (a \\documentclass and a \\begin{document}), shallowest first, as paths relative to root."""
    found = []
    for dirpath, dirs, files in os.walk(root):
        rel = Path(dirpath).relative_to(root)
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and d not in INIT_SKIP_DIRS)
        if len(rel.parts) >= depth:
            dirs[:] = []
        for f in sorted(files):
            if f.endswith(".tex"):
                try:
                    t = (Path(dirpath) / f).read_text(errors="replace")[:300000]
                except OSError:
                    continue
                if "\\documentclass" in t and "\\begin{document}" in t:
                    found.append((rel / f).as_posix())
    return sorted(found, key=lambda p: (len(Path(p).parts), p))


def guess_paper_name(main, root_name, used):
    """A name for a paper: its directory's or file's name unless that is generic (paper/main.tex), then the project's."""
    generic = {"", ".", "paper", "papers", "tex", "src", "doc", "docs", "main", "article", "manuscript", "ms", "index", "root"}
    p = Path(main)
    base = next((x for x in (p.parent.name, p.stem, root_name) if x.lower() not in generic), "paper")
    base = slug(base, "paper")
    name, i = base, 2
    while name in used:
        name, i = f"{base}{i}", i + 1
    return name


def scan_results(root, main, texinputs, generated):
    """Labels of the theorem-like results of a paper, in document order (what `uncovered` would list for an empty ledger)."""
    search = [(root / d).resolve() for d in texinputs]
    files, _ = tex_sources(root / main, search, [(root / d).resolve() for d in generated])
    extra_stmt, extra_result, _ = discover_theorem_envs(files)
    seen, out = set(), []
    for f in files:
        if f.suffix != ".tex":
            continue
        text = strip_comments(f.read_text(errors="replace"))
        for lab in result_labels(text, find_environments(text, extra_stmt), extra_result):
            if lab not in seen:
                seen.add(lab)
                out.append(lab)
    return out


def claim_names(labels):
    used, out = set(), {}
    for lab in labels:
        base = slug(lab.split(":", 1)[-1], "claim")
        if base in used:
            base = slug(lab, "claim")
        name, i = base, 2
        while name in used:
            name, i = f"{base}{i}", i + 1
        used.add(name)
        out[lab] = name
    return out


def init_plan(root, args, ask=None):
    """Everything `init` would write, as {relative path: text}, plus notes for the person. `ask(prompt, default)` is used for
    what is not given and is not obvious (None: never ask, refuse instead)."""
    root = Path(root).resolve()
    notes, files = [], {}
    if (root / "ledger" / "ledger.toml").exists():
        raise LedgerError(f"{root / 'ledger' / 'ledger.toml'} exists: this directory already has a ledger (init never overwrites)")
    name = args.name or (ask("project name", slug(root.name, "project")) if ask else slug(root.name, "project"))
    # papers: NAME=path from --paper, else found
    papers = {}
    for spec in args.paper or []:
        n, _, m = spec.rpartition("=")
        m = Path(m).as_posix() if not Path(m).is_absolute() else Path(os.path.relpath(m, root)).as_posix()
        if not (root / m).is_file():
            raise LedgerError(f"--paper {spec}: {root / m} is not a file")
        papers[slug(n) if n else guess_paper_name(m, root.name, papers)] = m
    if not papers:
        cands = find_paper_mains(root)
        if len(cands) == 1:
            papers[guess_paper_name(cands[0], root.name, papers)] = cands[0]
        elif len(cands) > 1:
            if ask:
                print("main .tex files found:")
                for k, c in enumerate(cands, 1):
                    print(f"  {k}. {c}")
                pick = ask("which are papers of this ledger (numbers, comma separated)", "1")
                try:
                    chosen = [cands[int(x) - 1] for x in pick.replace(" ", "").split(",") if x]
                except (ValueError, IndexError):
                    raise LedgerError(f"not a list of numbers between 1 and {len(cands)}: {pick!r}")
            else:
                raise LedgerError("several main .tex files found; say which are papers with --paper NAME=path (repeatable):\n  "
                                  + "\n  ".join(cands))
            for c in chosen:
                papers[guess_paper_name(c, root.name, papers)] = c
        else:
            notes.append("no main .tex file found: add a [paper.NAME] with `main = \"path/to/main.tex\"` to ledger/ledger.toml")
    # where ledgercheck.sty is found
    here = Path(__file__).resolve().parent
    sty_dir = None
    if args.vendor:
        sty_dir = "ledger/vendor"
    elif (here / "tex" / "ledgercheck.sty").is_file() and root in (here / "tex").parents:
        sty_dir = Path(os.path.relpath(here / "tex", root)).as_posix()
    else:       # outside the project, a path would differ from machine to machine
        notes.append("ledgercheck.sty is not inside this project: run `init --vendor` (or copy it in) and put its directory into "
                     "`texinputs` of [paper.NAME]; the paper and `review` need it")
    # a key (optional)
    key = None
    if args.key:
        kf = Path(args.key).expanduser()
        if not kf.is_file():
            raise LedgerError(f"--key {args.key}: no such file (give the public key, *.pub)")
        person = args.person or (ask("your name (as it appears under attestations)", git_user_name()) if ask else "")
        if not person:
            raise LedgerError("--key needs --person NAME")
        pub = kf.read_text().strip()
        word = next((w for w in person.split() if len(re.sub(r"[^A-Za-z]", "", w)) >= 3), "")   # "A. Cook" -> cook
        kid = slug(args.key_id or word.lower(), "me")
        key = (kid, person, pub)
    gen = {}
    for n, m in papers.items():
        d = Path(m).parent
        gen[n] = ("ledger" if d.as_posix() == "." else d.as_posix() + "/ledger")
    if any(g == "ledger" for g in gen.values()):          # a paper in the project root: its generated files cannot go into ledger/
        for n in gen:
            if gen[n] == "ledger":
                gen[n] = "ledger/generated"
        notes.append("a paper sits in the project root: its generated files go to ledger/generated; add that directory to TEXINPUTS "
                     "when building the paper (or move the paper into its own directory)")
    lines = [f"# Trust ledger of {name}. Written by `ledger.py init`; edit freely (format: docs/FORMAT.md of trust-ledger).",
             "[project]", f"name = {json.dumps(name)}", ""]
    for n, m in papers.items():
        lines += [f"[paper.{n}]", f"main = {json.dumps(m)}"]
        if sty_dir:
            lines.append(f"texinputs = {json.dumps([sty_dir])}   # where ledgercheck.sty is found; also used by `review`")
        if key:
            lines.append(f"authors = {json.dumps([key[0]])}   # key ids: the people who vouch for this paper")
        lines.append("")
    if papers:
        lines += ["[generated]", f"dirs = {json.dumps(sorted(set(gen.values())))}   # written by `ledger.py -P NAME tex`; never part of the hashed source", ""]
    if not args.no_checklist:
        lines += [INIT_CHECKLIST]
    lines += ["# Machine-checked evidence comes in through adapters, for example Lean (see examples/ in trust-ledger):",
              "# [adapter.lean]", '# prefix = "lean:"', '# dump = "lean.json"',
              '# extract = "ledger/dump.sh | python3 ledger/vendor/lean.py"', ""]
    files["ledger/ledger.toml"] = "\n".join(lines)
    # claims: one skeleton per labelled result
    total = 0
    claims = ["# The results of the paper(s). A claim without `evidence` counts as an assertion (E5) until a check is recorded.",
              '# To record one: `evidence = "E1"` and, for Lean, `lean = ["Namespace.theorem"]` (see examples/ in trust-ledger).', ""]
    if not args.no_claims:
        for n, m in papers.items():
            try:
                labels = scan_results(root, m, [], [gen[n]])
            except OSError as e:
                notes.append(f"paper {n}: could not be read ({e}); no claims were generated for it")
                continue
            names = claim_names(labels)
            for lab in labels:
                claims += [f"[claim.{names[lab]}]", f"label = {json.dumps(lab)}", f"paper = {json.dumps(n)}", ""]
            total += len(labels)
            if not labels:
                notes.append(f"paper {n}: no labelled theorem-like results found; add [claim.NAME] entries by hand")
    files["ledger/claims.toml"] = "\n".join(claims)
    if key:
        files["ledger/keys.toml"] = toml_record(f"[key.{key[0]}]", dict(person=key[1], public=key[2], source="paper")).lstrip("\n")
    files["ledger/README.md"] = (
        "# ledger/\n\nThe trust ledger of this project (tool: `ledger.py` of trust-ledger).\n\n"
        "* `ledger.toml`: papers, checklist, adapters. `claims.toml`: the results the papers state. Both are edited by hand.\n"
        "* `keys.toml` and `attestations.toml`: who vouches for what (`ledger.py addkey`, `ledger.py attest`).\n"
        "* `lock*.json`, `*.json` dumps and `snapshots/` are written by the tool; commit them.\n\n"
        "    python3 ledger.py -P NAME status      # what is attested, what is not\n"
        "    python3 ledger.py -P NAME lock        # write the lock file, print the root\n")
    return dict(root=root, name=name, papers=papers, files=files, notes=notes, claims=total, key=key, vendor=args.vendor,
                sty_dir=sty_dir, generated=gen)


def cmd_init(L, args):
    """Bootstrap a ledger in the project directory (-C DIR, default: the current directory)."""
    root = Path(args.dir).resolve()
    interactive = sys.stdin.isatty() and not args.yes and not args.dry_run

    def ask(prompt, default):
        if not interactive:
            return default
        a = input(f"{prompt} [{default}]: " if default else f"{prompt}: ").strip()
        return a or default
    plan = init_plan(root, args, ask=ask if interactive else None)
    if interactive and not args.key:
        cands = sorted(Path.home().glob(".ssh/*.pub"))
        if cands:
            print("public keys found:", ", ".join(c.name for c in cands))
            kf = input("register one as an author key now (path, or Enter to skip; `ledger.py addkey` does it later): ").strip()
            if kf:
                args.key = kf
                args.name = plan["name"]                            # keep the answers given so far: do not ask again
                args.paper = [f"{n}={m}" for n, m in plan["papers"].items()]
                plan = init_plan(root, args, ask=ask)
    for rel, text in plan["files"].items():
        print(("would write " if args.dry_run else "writing ") + rel)
    if args.dry_run:
        for n in plan["notes"]:
            print("note:", n)
        return 0
    (root / "ledger").mkdir(exist_ok=True)
    for rel, text in plan["files"].items():
        (root / rel).write_text(text if text.endswith("\n") else text + "\n")
    if args.vendor:
        v = root / "ledger" / "vendor"
        v.mkdir(exist_ok=True)
        shutil.copy(Path(__file__), v / "ledger.py")
        sty = Path(__file__).resolve().parent / "tex" / "ledgercheck.sty"
        if sty.is_file():
            shutil.copy(sty, v / "ledgercheck.sty")
        else:
            plan["notes"].append("ledgercheck.sty was not found next to ledger.py and is not vendored")
        print("copied ledger.py" + (" and ledgercheck.sty" if sty.is_file() else "") + " to ledger/vendor/")
    # does what we wrote load?
    problems = []
    try:
        chk = Ledger(root)
        problems = chk.errors
        n_claims = len(chk.claims)
    except LedgerError as e:
        problems, n_claims = [str(e)], 0
    print(f"\nledger of {plan['name']!r}: {len(plan['papers'])} paper(s), {n_claims} claim(s)"
          + (f", author key {plan['key'][0]!r}" if plan["key"] else ""))
    for p in problems:
        print("problem:", p)
    for n in plan["notes"]:
        print("note:", n)
    first = next(iter(plan["papers"]), "NAME")
    print("\nnext steps:")
    print(f"  python3 ledger.py -P {first} status          # every result is 'none' until someone attests it")
    if not plan["key"]:
        print("  python3 ledger.py addkey ID --person \"Your Name\" --pub ~/.ssh/id_ed25519.pub     # to sign attestations")
    print(f"  python3 ledger.py -P {first} attest CLAIM --person \"Your Name\" --level green --sign KEYFILE --key ID")
    print(f"  python3 ledger.py -P {first} lock && python3 ledger.py -P {first} tex")
    print(f"  in the paper's preamble:  \\usepackage[paper={first}]{{ledgercheck}}")
    return 1 if problems else 0


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


def cmd_check(L, args):
    """Run every [check.*] command and record the results as the dump of the built-in `checks` adapter."""
    if not L.checks:
        sys.exit("no [check.NAME] tables in ledger/")
    nodes, failed = {}, 0
    for n, ch in sorted(L.checks.items()):
        out = subprocess.run(ch["command"], shell=True, cwd=L.root, text=True, capture_output=True)
        ok = out.returncode == 0
        failed += not ok
        print(f"check {n}: {'pass' if ok else 'FAIL (exit %d)' % out.returncode}")
        code = L.code_hashes(ch)
        env = dict(environment=L.env_hash()) if ch.get("environment") else {}   # only a check that declares it
        nodes[n] = dict(kind="check", status="ok" if ok else "failed", word="pass" if ok else "fail",
                        content=dict(name=n, command=ch["command"], code=code,
                                     inputs={x: L.input_hash(x) for x in ch.get("inputs", [])},
                                     exit=out.returncode, stdout_sha256=hashlib.sha256(out.stdout.encode()).hexdigest(), **env),
                        spec=dict(name=n, command=ch["command"], code=code, **({"environment": True} if env else {})),
                        info=dict(stdout=out.stdout[-2000:], stderr=out.stderr[-2000:]))
    dump = dict(adapter="checks", version=__version__, nodes=nodes, title="Check",
                labels={"pass": "pass", "fail": "fail"},
                legend="pass/fail = the check script, which tests the result against its data, exits with 0 / "
                       "another code on the recorded inputs.")
    (L.dir / "checks.json").write_text(json.dumps(dump, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
    print(f"wrote {L.dir / 'checks.json'}" + (f"; {failed} check(s) failed (recorded as such)" if failed else ""))
    return 0


def step_order(steps, producer):
    """Steps in an order where every step comes after the steps that produce its inputs."""
    after = {n: {producer[x] for x in st.get("inputs", []) if x in producer} - {n} for n, st in steps.items()}
    order = []
    while after:
        ready = sorted(n for n, d in after.items() if not d)
        if not ready:
            sys.exit(f"steps depend on each other in a cycle: {', '.join(sorted(after))}")
        order += ready
        after = {n: d - set(ready) for n, d in after.items() if n not in ready}
    return order


def cmd_reproduce(L, args):
    """Re-run the command steps in a scratch copy of the project and compare their outputs with the ones in it."""
    if not L.steps:
        sys.exit("no [step.NAME] tables in ledger/")
    unknown = set(args.steps) - set(L.steps)
    if unknown:
        sys.exit(f"unknown step(s): {', '.join(sorted(unknown))}")
    ignore = L.cfg.get("reproduce", {}).get("ignore", [".git", "__pycache__", ".lake", "node_modules"])
    tmp = Path(tempfile.mkdtemp(prefix="ledger-reproduce-"))
    bad = 0
    try:
        work = tmp / "p"
        shutil.copytree(L.root, work, symlinks=True, ignore=shutil.ignore_patterns(*ignore))
        for n in step_order(L.steps, L.producer):
            st = L.steps[n]
            if args.steps and n not in args.steps:
                continue
            if st.get("manual"):
                print(f"step {n}: manual ({st.get('person', '?')}), not re-run; its outputs are taken as given")
                continue
            paths = [L.sources[x[7:]].get("path") if x.startswith("source:") else x for x in st.get("inputs", [])]
            absent = [x for x, q in zip(st.get("inputs", []), paths) if not q or not (work / q).exists()]
            if absent:
                print(f"step {n}: inputs not available here ({', '.join(absent)}), not re-run")
                continue
            for out in st.get("outputs", []):  # a command that does nothing must not pass
                q = work / out
                shutil.rmtree(q) if q.is_dir() else q.unlink(missing_ok=True)
            run = subprocess.run(st["command"], shell=True, cwd=work, text=True, capture_output=True)
            if run.returncode:
                bad += 1
                print(f"step {n}: FAILED (exit {run.returncode})\n" + (run.stderr or run.stdout)[-1500:])
                continue
            res = []
            for out in st.get("outputs", []):
                q = work / out
                if not q.exists():
                    res.append(f"{out} NOT PRODUCED"); bad += 1
                elif st.get("compare", "bytes") == "none":
                    res.append(f"{out} produced (not compared: compare = none)")
                elif not (L.root / out).exists() or digest(q) != digest(L.root / out):
                    res.append(f"{out} DIFFERS from the one in the project"); bad += 1
                else:
                    res.append(f"{out} identical")
            print(f"step {n}: " + "; ".join(res))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("reproduced" if not bad else f"{bad} problem(s): the outputs in the project are not what the steps produce")
    return 1 if bad else 0


def cmd_commitment(L, args):
    """Print the salted commitment to a file or directory, creating the salt file if it does not exist.
    Paths are relative to the project root (-C), like everywhere in the ledger."""
    root = Path(args.dir)
    salt_file, data = root / args.salt_file, root / args.path
    if not salt_file.exists():
        import secrets
        salt_file.parent.mkdir(parents=True, exist_ok=True)
        salt_file.write_text(secrets.token_hex(32) + "\n")
        salt_file.chmod(0o600)
        print(f"created {salt_file}: keep it private, with the data; anyone with data and salt can check the commitment",
              file=sys.stderr)
    print(f'commitment = "{commitment(read_salt(salt_file), digest(data))}"')
    return 0


def cmd_migrate(L, args):
    """Rebind unsigned attestations from the statement hashes of an older format (FORMAT.md 6). The old lock file
    must have been current (old `verify` OK) when the dumps and ledger.toml were converted."""
    old = json.loads(Path(args.old_lock).read_text())
    if old.get("format") not in (0, "0.1.0", "0.2.0"):
        sys.exit(f"{args.old_lock}: format {old.get('format')!r}; migrate reads lock files of format 0.1.0 and 0.2.0")
    pairs = [(old["claims"].get(n, {}).get("spec"), L.cspec[n]) for n in L.claims]
    pairs += [(old.get("hypotheses", {}).get(h, {}).get("spec"), L.hspec[h]) for h in L.scope_hyps]
    new = {}
    for o, n in pairs:
        if o and new.setdefault(o, n) != n:
            sys.exit(f"old statement hash {o[:12]} maps to two new ones; rebind by hand")
    rebound, signed = 0, []
    for f in sorted(L.dir.glob("*.toml")):
        blocks = re.split(r"(?m)^(?=\[)", f.read_text())
        out = []
        for b in blocks:
            m = re.search(r'(?m)^bound = "([0-9a-f]{64})"$', b)
            if b.startswith("[[attestation]]") and m and m.group(1) in new:
                if re.search(r"(?m)^sig = ", b):
                    signed.append(re.search(r'(?m)^(?:claim|hypothesis) = "(.*)"$', b).group(1))
                else:
                    b = b.replace(m.group(0), f'bound = "{new[m.group(1)]}"'); rebound += 1
            out.append(b)
        if "".join(out) != f.read_text():
            f.write_text("".join(out))
    print(f"rebound {rebound} attestation(s) to format {FORMAT_VERSION} statement hashes")
    for x in signed:
        print(f"signed attestation on {x} not rebound: the signature covers the old binding; ask the signer to attest again")
    print(f"now run `ledger.py{' -P ' + L.paper if L.paper else ''} lock`")
    return 0


def cmd_verify_attestation(L, args):
    """Check a standalone attestation file against a lock file (hash only; no ledger sources needed)."""
    t = tomllib.loads(Path(args.file).read_text())
    lock = read_lock(args.lock)
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
    ac = {k: v for k, v in L.cfg.get("adapter", {}).items() if v.get("extract")}
    if not ac:
        sys.exit("no extract command configured ([adapter.NAME] extract = ...)")
    for name, cfg in ac.items():  # stdin: every reference the claims make into this adapter; stdout: its dump
        refs = sorted({r for c in L.claims.values() for r in c.get(name, [])})
        out = subprocess.run(cfg["extract"], shell=True, cwd=L.root, input="\n".join(refs), text=True, capture_output=True)
        sys.stderr.write(out.stderr[-3000:])
        if out.returncode:
            return out.returncode
        dump = json.loads(out.stdout)
        problems = check_dump(dump)
        if problems:
            sys.exit(f"adapter {name}: the extractor wrote an invalid dump:\n  " + "\n  ".join(problems[:20]))
        dump["env_hash"] = L.env_hash()  # lets later runs notice that the sources moved on
        (L.dir / cfg.get("dump", name + ".json")).write_text(json.dumps(dump, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--version", action="version", version=f"trust-ledger {__version__} (format {FORMAT_VERSION})")
    ap.add_argument("-C", dest="dir", default=".")
    ap.add_argument("-P", "--paper", default=None, help="restrict to the claims of one configured paper (own root and lock file)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("status"); p.add_argument("--strict", action="store_true")
    p.add_argument("--json", action="store_true", help="print the status as JSON (claims, hypotheses, messages) instead of the table")
    sub.add_parser("lock"); sub.add_parser("verify"); sub.add_parser("extract"); sub.add_parser("tex")
    p = sub.add_parser("review", help="build a review packet: paper statements next to back-translations and Lean text")
    p.add_argument("--claims", help="comma-separated claim names (default: all in scope)")
    p.add_argument("--for", dest="for_", metavar="TARGETS",
                   help="comma-separated labels or claim names: those claims and everything they rest on (uses, Lean steps)")
    p.add_argument("--out", help="output directory (default: [review] out, else ./review)")
    p.add_argument("--aux", help="use this .aux of the paper instead of building the paper once")
    p.add_argument("--no-lean", action="store_true", help="leave the Lean source text out")
    p.add_argument("--defs-inline", action="store_true",
                   help="repeat the definitions with every claim (default: once, in a section Definitions)")
    p = sub.add_parser("why"); p.add_argument("claim")
    p = sub.add_parser("attest"); p.add_argument("claim", nargs="?"); p.add_argument("--person", required=True)
    p.add_argument("--hypothesis", help="attest a hypothesis (e.g. that it is a known theorem) instead of a claim")
    p.add_argument("--level", required=True, choices=LEVELS); p.add_argument("--reason"); p.add_argument("--checklist")
    p.add_argument("--sign", metavar="PRIVATE_KEY", help="sign with this ssh key file (ssh-keygen -Y sign)")
    p.add_argument("--key", help="id of the signing key in ledger/keys.toml")
    p.add_argument("--pub", help="public key file (standalone attestations by someone who is not in keys.toml)")
    p.add_argument("--no-snapshot", action="store_true", help="do not record what the attestation binds to (ledger/snapshots/)")
    p.add_argument("--out", help="write a standalone attestation file instead of appending to ledger/attestations.toml")
    p = sub.add_parser("assess", help="record a model's assessment of a claim together with the state it judged (or --bind an existing one)")
    p.add_argument("claims", nargs="*", metavar="CLAIM")
    p.add_argument("--audit", action="store_true", help="for assessments that name no state: say from git whether what they compared changed since")
    p.add_argument("--bind-unchanged", action="store_true", help="with --audit: bind those where nothing changed (you assert that they still fit)")
    p.add_argument("--verdict", choices=ASSESSMENT_VERDICTS); p.add_argument("--model"); p.add_argument("--date")
    p.add_argument("--notes-file", help="the assessment's text, a LaTeX fragment"); p.add_argument("--notes")
    p.add_argument("--bind", action="store_true", help="mark existing assessments as describing the present state of their claims")
    p = sub.add_parser("snapshot", help="record what current attestations bind to, so that `diff` can show later changes")
    p.add_argument("targets", nargs="*", metavar="CLAIM", help="with --from-git: only these claims")
    p.add_argument("--from-git", action="store_true", help="also rebuild the snapshots of stale attestations from the git history")
    p.add_argument("--depth", type=int, default=8, help="with --from-git: how many earlier commits to try (default 8)")
    p.add_argument("--dry-run", action="store_true", help="say what would be recorded or recovered, write nothing")
    p.add_argument("--partial", action="store_true", help="with --from-git: where the exact state cannot be rebuilt (evidence not in git), keep the statement text as an unverified snapshot")
    p = sub.add_parser("diff", help="what changed since the latest attestation (of a claim, or --hypothesis) that has a snapshot")
    p.add_argument("claim", nargs="?"); p.add_argument("--hypothesis")
    p = sub.add_parser("init", help="bootstrap a ledger in the project directory (-C DIR): ledger.toml, claims from the paper's labels, keys")
    p.add_argument("--name", help="project name (default: the directory's name)")
    p.add_argument("--paper", action="append", metavar="NAME=MAIN.tex", help="a paper of the ledger (repeatable); default: the main .tex file found")
    p.add_argument("--no-claims", action="store_true", help="do not generate a claim for every labelled theorem-like result")
    p.add_argument("--no-checklist", action="store_true", help="do not write the default checklist")
    p.add_argument("--key", metavar="PUBKEY", help="register this public key as an author key of the paper(s)")
    p.add_argument("--person", help="the key owner's name (with --key)"); p.add_argument("--key-id", help="id of the key (default: first name)")
    p.add_argument("--vendor", action="store_true", help="copy ledger.py and ledgercheck.sty into ledger/vendor/ (the project carries its own tool)")
    p.add_argument("--yes", action="store_true", help="never ask: take the defaults, refuse when something is ambiguous")
    p.add_argument("--dry-run", action="store_true", help="say what would be written, write nothing")
    p = sub.add_parser("addkey"); p.add_argument("id"); p.add_argument("--person", required=True)
    p.add_argument("--pub", required=True, help="public key file or line")
    p.add_argument("--source", choices=("paper", "vouched", "url"), default="paper")
    p.add_argument("--url"); p.add_argument("--vouched-by")
    p = sub.add_parser("verify-attestation"); p.add_argument("file"); p.add_argument("--lock", required=True)
    p = sub.add_parser("reproduce", help="re-run the command steps in a scratch copy, compare their outputs")
    p.add_argument("steps", nargs="*", help="only these steps (default: all, in dependency order)")
    sub.add_parser("check", help="run the [check.NAME] commands, record their results (ledger/checks.json)")
    p = sub.add_parser("commitment", help="salted commitment to data that is not published (FORMAT.md 3.4)")
    p.add_argument("path"); p.add_argument("--salt-file", required=True, help="created with a random salt if missing")
    p = sub.add_parser("migrate", help="rebind attestations after a format change, from the old lock file")
    p.add_argument("--old-lock", required=True, help="lock file written by the previous format, current when converting")
    args = ap.parse_args(argv)
    try:
        return run(args)
    except LedgerError as e:
        sys.exit(str(e))


def run(args):
    if args.cmd == "commitment":
        return cmd_commitment(None, args)
    if args.cmd == "init":
        return cmd_init(None, args)
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
