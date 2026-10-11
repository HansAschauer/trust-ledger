#!/usr/bin/env python3
"""DVC import for trust-ledger: the stages of dvc.yaml as [step.*] tables (docs/FORMAT.md 3.4).

  python3 adapters/dvc_steps.py [dvc.yaml] > ledger/steps-dvc.toml

Needs PyYAML (the ledger itself does not). Each stage becomes a step with its `cmd` as command
(several commands joined with &&, `wdir` applied), its `outs`, `metrics` and `plots` as outputs, its
`deps` as inputs, except scripts (by file extension), which go to `code` and so are hashed as the
definition of the step, and the files of its `params` as further inputs. Data that no stage produces
(e.g. tracked with `dvc add`) stays a plain file input; declare it as a [source.*] to give it a URL,
licence or commitment. `foreach`/`matrix` stages are not supported and are reported.

Regenerate the file whenever dvc.yaml changes; the ledger hashes it like any hand-written step table.
"""
import json, posixpath, sys

VERSION = "0.2.0"
CODE = (".py", ".r", ".R", ".jl", ".sh", ".m", ".ipynb", ".do", ".sas", ".sql", ".qmd", ".Rmd")


def paths(entries):
    """dvc lists paths as strings or as {path: options}."""
    out = []
    for e in entries or []:
        out += [e] if isinstance(e, str) else list(e)
    return out


def stage_step(name, st):
    if "foreach" in st or "matrix" in st:
        raise ValueError(f"stage {name}: foreach/matrix stages are not supported; write its steps by hand")
    wdir = st.get("wdir", ".")
    at = lambda p: posixpath.normpath(posixpath.join(wdir, p))
    cmd = st["cmd"] if isinstance(st["cmd"], str) else " && ".join(st["cmd"])
    deps = [at(p) for p in paths(st.get("deps"))]
    params = []
    for e in st.get("params", []) or []:
        params += ["params.yaml"] if isinstance(e, str) else list(e)  # a key of params.yaml, or {file: [keys]}
    outs = [at(p) for k in ("outs", "metrics", "plots") for p in paths(st.get(k))]
    step = dict(command=cmd if wdir == "." else f"cd {wdir} && {cmd}",
                code=sorted(p for p in deps if p.endswith(CODE)),
                inputs=sorted({p for p in deps if not p.endswith(CODE)} | {at(p) for p in params}),
                outputs=sorted(set(outs)))
    return {k: v for k, v in step.items() if v}


def convert(doc):
    out = [f"# generated from dvc.yaml by adapters/dvc_steps.py {VERSION}; do not edit, regenerate after changing dvc.yaml"]
    for name, st in (doc.get("stages") or {}).items():
        out.append(f"\n[step.{json.dumps(name)}]")
        out += [f"{k} = {json.dumps(v, ensure_ascii=False)}" for k, v in stage_step(name, st).items()]
    return "\n".join(out) + "\n"


def main():
    try:
        import yaml
    except ImportError:
        sys.exit("adapters/dvc_steps.py needs PyYAML (pip install pyyaml)")
    try:
        print(convert(yaml.safe_load(open(sys.argv[1] if len(sys.argv) > 1 else "dvc.yaml"))), end="")
    except ValueError as e:
        sys.exit(str(e))


if __name__ == "__main__":
    main()
