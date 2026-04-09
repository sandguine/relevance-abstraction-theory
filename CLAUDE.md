# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A theory about how agents relate and cooperate with one another, formalized in Coq. The verification lives under `verification/coq/StrategicAbstraction/`.

## Coq Build

To scaffold the directory structure (already done — stubs exist):

```bash
cd verification && bash make_coq_structure.sh
```

To compile Coq proofs, you need a `_CoqProject` file and `coq_makefile`. Typical workflow once `_CoqProject` is set up:

```bash
cd verification/coq
coq_makefile -f _CoqProject -o Makefile
make          # compile all
make <File>.vo  # compile a single file
```

To check a single file interactively, open it in CoqIDE or VS Code with the VSCoq extension.

## Module Architecture

All Coq source lives under `verification/coq/StrategicAbstraction/` with five modules:

- **Core** — foundational definitions: Markov games, policies, value functions, soft best-response, strategic divergence, and the Strategic Equivalence Certificate (SEC).
- **Certificates** — proof certificates: occupancy measures, performance difference lemma, Distributional SEC (DSEC), entropy bridge.
- **InfoNCE** — contrastive learning layer: loss function, optimal critic, Rademacher complexity, VC-dimension classification.
- **Phenomena** — derived results: horizon equivalence, diversity.
- **ImplementationSketch** — algorithm outlines and diagnostic utilities.

The dependency order is: `Core` → `Certificates` → `InfoNCE` → `Phenomena` / `ImplementationSketch`.
