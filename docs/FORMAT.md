# Ledger format, version 0.1.0 (alpha)

This file is the normative part. `ledger.py` is one implementation; anyone can write another
that produces the same hashes. Nothing here depends on Lean or on Python.

The format is versioned separately from the tool (semantic versioning). While the major version is 0,
any minor version may change hashes; a patch version never does. The domain tag `trust-ledger/0` in
section 2 names the major version only. Every lock file records the format version it was written in
(section 5).

## 1. Nodes

A ledger is a directed graph of nodes. A node has

| field        | meaning |
|--------------|---------|
| `id`         | unique string, e.g. `lean:Toy.thm`, `claim:thm-twice`, `file:scripts/check.py` |
| `kind`       | core: `lean-decl`, `file`, `paper-source`, `claim`, `citation`, `assertion`, `attestation`, `key`, `hypothesis`, `reading`, `assessment`, `environment`; adapters add their own (section 2.6) |
| `provenance` | `computed` (derived from an artefact by a tool), `asserted` (written by a human), `generated` (written by a model) |
| `content`    | JSON object; what the node *is* (statement text, file digest, ...) |
| `deps`       | list of node ids this node rests on |

Provenance is part of the hashed data: an asserted node cannot later be relabelled as computed
without changing every hash above it.

## 2. Hashing

* Hash function: SHA-256, written as 64 lowercase hex digits.
* Canonical JSON: UTF-8, object keys sorted by code point, separators `,` and `:`, no whitespace,
  no floats (integers, strings, booleans, null, arrays, objects only), strings not ASCII-escaped
  beyond what JSON requires.
* `H(tag, x) = SHA-256( "trust-ledger/0\0" + tag + "\0" + canonical_json(x) )`.

### 2.1 Graph hash

Both hashes below use one construction, `merkle(tag, payload, deps)`, over a graph whose nodes
have a JSON `payload` and a set of `deps` (ids). For a node `n` outside any cycle:

`h(n) = H(tag, {"p": payload(n), "deps": [[d, h(d)] for d in sorted(unique deps(n))]})`

Changing anything a node rests on changes its hash and the hash of every node above it.

If the graph has cycles, each strongly connected component C is hashed as one unit:
`h(C) = H(tag + "-scc", {"members": [[m, payload(m)] for m in sorted(C)], "deps": [[d, h(d)] for d in sorted external deps]})`,
and every member gets `h(m) = H(tag + "-member", [m, h(C)])`. A node with a self-dependency counts as a cycle.

### 2.2 Full hash and specification hash

`full(n) = h` with `tag = "node"`, `payload = {kind, provenance, content}` and the node's `deps`.
Lean declarations additionally depend on the environment node.

Some nodes have a second hash `spec(n)` that covers only what the node *says*, not how it was
shown. For `lean-decl` nodes, `spec` uses `tag = "spec"`, payload
`{name, kind, type, type_term, value, value_term}` (absent fields are `""`; `*_term` are exact
serialisations of kernel terms, `type`/`value` pretty-printed) and `deps = stmt_deps`, the
declarations occurring in the statement, or, for a definition, in its type and value.
**Proofs of theorems do not enter `spec`.** By proof irrelevance a refactored proof does not
change what a theorem claims. A human attestation is bound to `spec`; the proof itself is covered
by `full` and by the kernel check.

A claim's spec hash uses `tag = "claim-spec"`, payload
`{text, lean: [[name, spec(decl)]], others: [[id, full(id)] for file, citation and assertion nodes]}`
and `deps = uses` (other claims). A changed statement therefore also resets the attestations of
every claim that `uses` it.

### 2.3 Lean content

`content` of a `lean-decl` is everything the extractor reports (`lean/Dump.lean`) except
`stmt_deps`, `proof_deps`, `line` and `module`: name, kind, `type`, `type_term`, `value`,
`value_term`, `proof_term`, axioms, sorry, assumptions. A theorem without a proof term is an
error, not an empty proof.

### 2.4 Paper source and statements

A `paper-source` node (`computed`) has content `{main, files: {path: sha256}, unresolved: [...]}`.
`files` is `main` plus every file reached by `\input`/`\include` (resolved like TeX: relative to the
directory of `main`, then the configured `texinputs`; `.tex` appended when missing) and every `.bib`
named by `\bibliography`, and every local `.sty` named by `\usepackage`/`\RequirePackage` (resolved the same
way, searched recursively; packages not found locally belong to the TeX distribution and are not listed), in raw bytes, **minus everything below a `generated` directory**. Generated
files (the root file, the status table) are derived from the ledger, so hashing them would be circular.
Names that cannot be resolved are listed in `unresolved`, not silently ignored.

A claim with `labels` (or `label`) takes its statement from the paper: for each label, the text of the
innermost statement environment (`theorem`, `lemma`, ... ) or display-math environment containing
`\label{...}`, with comments and `\label`s removed and whitespace collapsed, prefixed by the
environment name and the label. The concatenation is the claim's `text` (source `tex`); without labels
the hand-written `text` is used (source `manual`). Macros are not expanded. A label that cannot be found
is an error. Because the text enters the claim's spec hash, **editing a theorem in the paper resets the
attestations on it**, while edits to prose or comments change only the paper-source node and the root.

### 2.5 Scopes

With a paper selected (`-P name`) the ledger keeps the claims whose `paper` is that paper or unset, plus
every claim they `uses`, and only the nodes these rest on. Each paper has its own root and its own lock
file (`lock-<paper>.json`; `lock.json` without a scope), so changes to the other paper's claims do not
change this paper's root. Root kinds are `claim`, `attestation`, `environment` and `paper-source`.

### 2.6 Adapter dumps

Evidence that a field-specific tool produces (a model checker, a data pipeline, a statistics run) enters
the ledger through an *adapter*: any program, in any language, that writes a JSON dump of this shape. The
core needs no knowledge of the tool; it hashes what the dump says.

```json
{"adapter": "proverif", "version": "0.1.0",
 "nodes": {"<reference>": {"kind": "...", "content": {...}, "deps": ["<reference>", ...],
                           "spec": {...}, "status": "ok|open|failed", "word": "...",
                           "register": ["<kind>:<name>", ...]}}}
```

* An adapter is configured as `[adapter.<name>]` in `ledger.toml` with `dump` (file below `ledger/`,
  default `<name>.json`), optional `prefix` (default `<name>:`) and optional `extract` (a command that
  reads the references of all claims on stdin, one per line, and writes the dump on stdout).
  `<name>` must not be a claim field (section 3).
* A claim refers to adapter nodes by listing references under the adapter's name, e.g.
  `proverif = ["model.pv#attacker(s)"]`. A reference that is not in the dump is an error.
* Every dump node becomes a node with id `prefix + reference`, `provenance` `computed`, the given `kind`
  (not one of the core kinds of section 1) and `content`, and `deps` = the prefixed references in
  `deps`, which must be in the same dump. Nodes no root rests on are dropped, as everywhere.
* `spec` (optional) is what the node *states*, as opposed to how it was obtained: the analogue of a Lean
  statement versus its proof. With `spec`, the node has `spec(n) = h` with `tag = "spec"`, payload
  `{kind, content: spec}` and the `deps` that have a `spec` themselves, and a claim's spec hash uses
  `spec(n)` for it; without `spec`, it uses `full(n)`. So whether a change resets the attestations on a
  claim is the adapter's decision, made once per node kind.
* `status`, `word` and `register` are not hashed. A claim shows, per adapter, the `word` (else the
  `status`) of its worst reference (`failed` > `open` > `ok`), or `missing`. `register` items enter the
  claim's register (section 4) like Lean axioms do.
* An invalid dump contributes no nodes; its problems are errors.

Example: `adapters/proverif.py`. A `proverif-query` node covers one named `query` of one `.pv` file:
content `{file, sha256, query, result}`, where `query` is the literal query text as written in the source
and `result` is `true`, `false` or `cannot be proved` (status `ok`, `failed`, `open`). There is no `spec`
and no `deps`: the file's hash covers the whole model. Its register item `model:<file>` records that a
ProVerif result is evidence type E1 *relative to the model*, and the model itself is what a reader must
judge faithful to the protocol it claims to describe.

## 3. Human files

Human-written nodes live in TOML files below `ledger/`, one table per node (see
`examples/toy/ledger/`). Computed nodes are never written by hand; they are recomputed.

* `[claim.<name>]`: `text` (statement as in the paper), optional `label` (LaTeX label), `evidence`
  (declared type E1..E5), `lean` (declaration names), `files` (paths), `uses` (other claims), `cites` (citation names), `note` (free text, not hashed), and
  for each configured adapter a list of references under its name (section 2.6). Any other field is an error.
* **One claim per label.** A labelled result of the paper is carried by exactly one claim, whose Lean
  declarations state *the whole result*. For a result with several parts, the project writes one Lean theorem
  that is the conjunction of the parts and lists that theorem. A claim for a lemma used on the way may
  exist, but it carries no label of the result it serves. `status` warns about any label carried by more than one claim
  (`split`). `why` and the review packet list the *steps*: claim A is a step of claim B when a declaration
  of A occurs in the transitive `stmt_deps` ∪ `proof_deps` closure of B's declarations. Steps are reported,
  not hashed: they are derived from the Lean dump.
* `[citation.<name>]`: `key`, `statement` (as used here), `source` (theorem number / page).
* `[assertion.<name>]`: `claim`, `text`; evidence type E5 by definition.
* `[[attestation]]`: `claim`, `person`, `date`, `level` (`green`, `yellow`, `conjecture`), `reason`
  (mandatory for yellow), `checklist` (items done, e.g. `["A1","A2"]`), `bound` (the claim's spec
  hash at the time of attesting).

An attestation is **stale** when `bound` differs from the claim's current spec hash. Stale
attestations are reported, never silently rewritten.

### 3.1 Keys and signatures (optional)

* `[key.<id>]`: `person`, `public` (an OpenSSH public key line), `source` (`paper` = introduced by the
  authors in this ledger, `vouched` = an author vouches, `url` = fetched from a page, with `url` and `fetched`),
  optional `vouched_by` (key ids) and `revoked` (date). Key nodes are `asserted` and hashed; a paper lists its
  author keys in `[paper.X] authors = [...]`, which makes them dependencies of the paper-source node.
* An attestation may carry `key` (a key id) and `sig`. The signed bytes are
  `"trust-ledger/0 attestation\n" + canonical_json({claim, person, date, level, reason, bound, checklist, project})`,
  signed with `ssh-keygen -Y sign -n trust-ledger-attestation`. The signature state is `signed` (valid),
  `unsigned`, `unknown-key` (counted as unsigned, with a warning), `unchecked` (no ssh-keygen),
  `revoked` (the attestation date is not before the key's `revoked` date) or `invalid`. Revoked and invalid
  attestations are ignored and reported. Attestation nodes include `key` and `sig`, so the root covers them.
* There is no certificate authority: the binding of a key to a person rests on the key list being published
  with the root under the authors' names (or on a source URL the reader can fetch again).
* A standalone attestation file (for example by an independent reviewer after publication) is a TOML fragment
  with one `[key.<id>]` and one `[[attestation]]`; `verify-attestation FILE --lock lock-<paper>.json` checks the
  signature against the key in the file and `bound` against the claim's spec hash in the lock file, without the
  ledger sources. A later version of the paper can include such a file in `ledger/`.

### 3.2 Hypotheses

A result proved in Lean *given* a hypothesis (a `Prop`-valued definition passed as an argument, listed to the
extractor with `assume=`) depends on it, and the register records `hyp:<Name>`. A hypothesis that occurs in an in-scope
result is a node of kind `hypothesis` (asserted) with content `{name, label, text, source, cites, note}`:

* `[hypothesis."<Name>"]`: `label` (the label in the paper of the lemma that states it informally; its text is taken
  from the paper like a claim's statement), `paper`, `cites` (citation names), optional `note` or `text`.
  Without an entry the hypothesis is still listed, with no label and no sources.
* Its spec hash is `H("hyp-spec", {text, lean: spec(Lean definition), cites: [[c, full(c)]]})`.
* An attestation with `hypothesis = "<Name>"` instead of `claim` is bound to it. A *current green* attestation says:
  this hypothesis is a known theorem of the cited literature; the person found the source, compared its statement
  with the formal definition and checked that the conditions match (checklist H1 to H3). It becomes stale when the
  statement in the paper, the Lean definition or a cited source changes.
* The register entry is **not** removed (the formalisation still assumes it, and `Reg` is unchanged). The status
  table shows `given hyp. [known thm.]` when all hypotheses of a result are so attested, `[some known thm.]` when
  some are, and a separate table lists every hypothesis with its attestation.

### 3.3 Generated aids: readings and assessments

A model's back-translation of a claim's Lean statement and a model's comparison of paper text, Lean statement and
back-translation are *generated* nodes (provenance `generated`) attached to the claim:

* `reading`: `{path, sha256, produced_by}`, one per claim, from the file `[review] readings` (a template with `{claim}`).
* `assessment`: `{claim, model, date, verdict, notes}` from `[assessment.<claim>]` tables; `verdict` is one of
  `consistent`, `partial` (faithful where formalised, but the claim covers only part of what the paper states under its
  label), `check`, `mismatch`, `unclear`; `notes` is a LaTeX fragment.
* They are dependencies of the claim, so they are covered by the root (the record shows which aids existed), but they
  are **excluded from the claim's spec hash**: regenerating a back-translation or an assessment never resets an
  attestation. Neither is an attestation: they say nothing about who stands behind the claim.

## 4. Register

`own(claim)` is computed from artefacts:

* `axiom:<name>` for each non-standard axiom of a declaration (`propext`, `Classical.choice`,
  `Quot.sound` are standard), `sorry` if `sorryAx` occurs;
* `hyp:<name>` for each declared assumption constant occurring as a hypothesis of a statement;
* `hyp:cited:<citation>` for each citation;
* the `register` items of the adapter nodes the claim refers to (e.g. `model:<file>` from ProVerif);
* `assertion:<name>` for each assertion on the claim;
* `evidence:none` if the claim has neither Lean declarations, adapter references nor files.

`Reg(c) = own(c) ∪ ⋃ Reg(u)` over `uses`, as a least fixed point (well defined on cycles).

## 5. Root and lock file

`root = H("root", [[n.id, full(n)] for all nodes of kind claim, attestation, environment, paper-source or
hypothesis, sorted by id])`. Citations, assertions, files and Lean declarations are covered through the
claims that depend on them.

`ledger/lock.json` stores all computed hashes and the root, together with `format` (the format version,
`"0.1.0"`) and `tool` (the version of the program that wrote it, informational). A lock file with
`format` `0` was written before versioning and is read as 0.1.0, whose hashing is the same. `verify`
refuses a lock file in a format it does not implement, recomputes everything from the artefacts and
fails on any difference. The root is what gets published (e.g. in the arXiv
comment field); see README.
