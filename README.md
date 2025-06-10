# Lean Subsequence Proof

This repository contains a Lean 4 proof of the subsequence pigeonhole principle theorem.

## Theorem

**Every sequence of n² + 1 distinct real numbers has a subsequence of length n + 1 that is either strictly increasing or strictly decreasing.**

## Files

- `subseq_pigeonhole.lean` - Main theorem proof using the pigeonhole principle
- `Subseq.lean` - Module entry point
- `Subseq/Basic.lean` - Basic definitions and lemmas
- `lakefile.lean` - Lake build configuration
- `lean-toolchain` - Lean version specification

## Building

Make sure you have [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) installed, then run:

```bash
lake exe cache get
lake build
```

## Status

🚧 **Work in Progress** - The proof is currently being developed and may contain incomplete sections or compilation errors.

## Dependencies

This project uses [Mathlib](https://github.com/leanprover-community/mathlib4) for standard mathematical definitions and theorems. 