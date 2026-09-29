---
name: Reproduction or proof-review report
about: Report a concrete build result or a concern about the finite theorem and its verification.
title: "Reproduction/review: "
---

## Scope

Which workflow did you inspect or run?

- Ordinary 116-module core library
- Complete finite certificate build and custom final assembly
- Concrete Mathlib corollary
- Source/statement/loader review only

## Exact release and environment

Release tag/commit and asset SHA-256:
Lean version and dependency-lock identity:
Operating system, RAM and relevant process limits:

## Commands and result

Give the exact command, failing module if any, and relevant log excerpt.
Remove credentials and personal machine paths before posting logs.
Distinguish configuration/hash checks from completed Lean compilation.

## Mathematical or verification concern

Name the source, declaration and precise assumption or checking step at issue.
Explain whether the concern is a statement mismatch, missing dependency,
kernel/loader behavior, build failure, attribution issue or something else.

## Completed checks

State exactly what passed and what did not run. A successful core build alone
does not reproduce the complete finite certificate theorem.
