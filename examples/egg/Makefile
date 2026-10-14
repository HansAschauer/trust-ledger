# Build order: extract (Lean dump) -> check (scripts) -> lock -> generate LaTeX -> compile.
PY ?= python3
L = $(PY) ../../ledger.py

.PHONY: all paper ledger verify reproduce clean
all: paper

ledger:
	$(L) extract
	$(L) check
	$(L) -P egg lock
	$(L) -P egg tex

paper: ledger
	cd paper && TEXINPUTS=ledger:../../../tex: latexmk -pdf -interaction=nonstopmode -quiet main.tex

verify:
	$(L) -P egg verify
	$(L) -P egg verify-attestation ledger/reader-attestation.toml --lock ledger/lock-egg.json

reproduce:
	$(L) reproduce

clean:
	cd paper && latexmk -C
