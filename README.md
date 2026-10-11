# Informed Search: River Crossing and Liquid Division

Two standalone Python programs adapted from the supplied PS1 teaching framework.
Both use A* with puzzle-specific heuristics, stable queue ordering, best-cost
tracking and parent records for solution reconstruction.

## Requirements

Python 3.10 or later. Only the Python standard library is required.

## Run

From this directory:

```sh
python Puzzle1.py --n 3 --capacity 2 --summary-only
python Puzzle1.py --n 4 --capacity 3 --summary-only
python Puzzle1.py --n 5 --capacity 3 --summary-only
python Puzzle2.py --summary-only
```

Omit `--summary-only` to display the full search trace. Use `--help` for options.
The default river heuristic is `boat-aware`; the default liquid heuristic is
`surplus-deficit`. Each program runs independently.

## Scope and provenance

This repository contains the program source and execution instructions.
The assignment report and recorded experimental evidence are supplied separately
in the coursework submission.

The programs retain and adapt the PS1 Board/Solver framework. Original framework
attributions are preserved in the source. AI assistance was used in development;
the coursework report describes its role and the verification performed.
