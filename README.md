# software

One repo for the clpi/software-* theses. Each former repo lives unchanged, with its full history,
under `theses/<name>/` (the repo name minus `software-`). Branches and PR heads of the old repos
are kept as `archive/<name>/...`.

- `CONSOLIDATION.md`: what overlapped, the layout, the stage-2 merges, the cutover steps.
- `consolidation/verify.py`: proves every old commit, ref, file and theorem is here.
- `run-gates.sh`: runs every thesis's gates.
