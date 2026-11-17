# DEBRIEF-math-erdos731

A DEBRIEF mission record (protocol https://github.com/Nervous-Machine/DEBRIEF) for **The claimed solution of Erdős Problem #731 (the least non-divisor of the central binomial coefficient)**.

This claim is on the public claims board, https://math-board.nervousmachine.com, which shows its stage, who has contributed, and what it needs next.

**Standing.** Certified 0. Accepted 0. Refuted 0. Open gaps 4. The claim and its public artifacts are pinned and the checks still owed are listed. Nothing has been built or run. Cycle 1 (2026-11-17) is a reading guide for the semantic questions, `trace/DEFINITIONAL-TRACE.md`; it changes no standing.

## The problem

For an integer n let A(n) be the least m that does not divide the central binomial coefficient (2n choose n). The authors say it is not hard to show that for almost all n, A(n) is exp((log n)^(1/2 + o(1))). The problem asks for a reasonable function f(n) with A(n) asymptotic to f(n) for almost all n.

Source: https://www.erdosproblems.com/731 (posed: Erdős, Graham, Ruzsa and Straus (1975)).

A third-party formalization of the problem statement exists: `FormalConjectures/ErdosProblems/731.lean` in github.com/google-deepmind/formal-conjectures at commit `e028240a61822d970c933f4656f51da025cf200b` (blob `1ca01c40151c0b9dd8c440437ab8b7663b34ad83`). It is the natural reference for whether a claimant's Lean theorem states this problem.

## The claim

**Eric Li**, using GPT-5.5 Pro (as listed by the claimant), submitted 2026-07-17 at https://www.erdosproblems.com/forum/thread/731/proof-claims.

The claim resolves the problem under an explicit dyadic-regularity formalisation of 'reasonable'. On each dyadic block it gives a scale F and proves two-sided tail bounds in natural density around it, so that log A(n) minus the main terms is tight in density, while no dyadically regular deterministic scale satisfies the requested asymptotic equivalence. The author presents this as a two-part answer: F is the best possible deterministic scale, and the equivalence as literally asked cannot hold for any dyadically regular f.

Artifacts, pinned:

- an arXiv preprint: arXiv:2606.29062v2 "A Resolution of Erdős Problem 731 under Dyadic Regularity" (published 2026-06-27, last revised 2026-07-26)
- a public repository: github.com/ericlisg/erdos731 at commit cb1b58c88bf639bb87664dd96ffc327c305e160e (2026-07-26); licence Apache-2.0; 130 Lean files; has a lakefile

Status on the problem page as of 2026-11-14: listed as one proof claim; not marked accepted by the site.

## What is owed

Each open gap is in `ASKS.md` with what closes it and who could act. In order:

1. **The Lean development has not been built or kernel-checked by anyone outside the claimant** (EG1): A rerun of the Lean build on an independent machine, written down first.
2. **Do the formal statements say what the problem asks?** (EG2): A mathematician who is not an author reads `trace/DEFINITIONAL-TRACE.md` against the claimant's statements and the problem page and signs or refuses checklist lines A1 to A3, in about half an hour. Two independent signatures close this gap.
3. **No independent mathematician has reported reading the proof, and there is no referee report** (EG3): Someone in the field reads it and says, under their name, what holds and what does not.
4. **Does the chosen formalisation of 'reasonable' answer the problem as posed?** (EG4): A number theorist answers checklist lines A4 and A5 of the trace under their name: the claim rules out every f whose logarithm is nearly constant on each block [X, 2X); would you count a function that swings by a fixed factor inside every block, such as F(n)(2 + sin(2π log₂ n)), as reasonable, and if so does the paper's argument extend to rule it out? Two independent signatures close this gap; a refusal names the function.

## Contributing

- **Rerun** (if there is a Lean development): copy `prereg_rerun.yaml`, fill in your predictions, register it with `tools/prereg.py register` from the protocol repository and commit it *before* running anything. Run. Report with the **Rerun report** issue form; it becomes a `rerun` cycle under your name.
- **Read**: the reading guide is `trace/DEFINITIONAL-TRACE.md` (cycle 1). It quotes the problem, the third-party formal statement and the claimant's statements, traces every symbol to its definition, records nine discrepancies, and ends with a five-line checklist (A1–A5, plus an optional A0). Sign or refuse it with the **Semantic read** issue form; your answers become a `read` cycle under your name. The single judgment that matters most is A4.
- **Run the worked examples**: `cycles/trace-1/Trace.lean` is written but has not been run by Lean. Anyone who builds the development (the rerun above) can run it with `lake env lean` and submit the output as a cycle.
- **Anything else**: open a plain issue.

Rules and templates: https://github.com/Nervous-Machine/DEBRIEF/blob/main/CONTRIBUTING.md. Every contribution is one dated cycle under your own name and goes into `CITATION.cff` and the next release.

## Layout

```
ledger/erdos731.json   the ledger (protocol 0.1.0)
claim.yaml            the pinned claim this record was opened from
SCORECARD.md / ASKS.md  generated from the ledger
prereg_rerun.yaml     a pre-registration template for the first rerun (unregistered)
prereg_trace.yaml     the pre-registration of cycle 1, the reading guide (hashed)
trace/                the reading guide for the semantic questions (cycle 1)
cycles/               contributed cycles, one file each
```

## Words

This record never calls the claim proved, verified or a theorem. It records what was claimed, what was checked by whom under what rule, and what is still open. Nothing here has standing until a cycle gives it one.
