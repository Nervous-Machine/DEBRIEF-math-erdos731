# DEBRIEF-math-erdos731

A DEBRIEF mission record (protocol https://github.com/Nervous-Machine/DEBRIEF) for **The claimed solution of Erdős Problem #731 (the least non-divisor of the central binomial coefficient)**.

**Standing.** Certified 0. Accepted 0. Refuted 0. Open gaps 4. This record is at tier zero: the claim and its public artifacts are pinned, the checks still owed are listed, and nothing has been run or read yet. The first contribution is open.

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
2. **Do the formal statements say what the problem asks?** (EG2): A reading of the formal statement against the problem as posed, by someone who did not write it.
3. **No independent mathematician has reported reading the proof, and there is no referee report** (EG3): Someone in the field reads it and says, under their name, what holds and what does not.
4. **Does the chosen formalisation of 'reasonable' answer the problem as posed?** (EG4): a number theorist reads the problem's source and the claim's definition and says, under their name, whether the resolved statement is the problem

## Contributing

- **Rerun** (if there is a Lean development): copy `prereg_rerun.yaml`, fill in your predictions, register it with `tools/prereg.py register` from the protocol repository and commit it *before* running anything. Run. Report with the **Rerun report** issue form; it becomes a `rerun` cycle under your name.
- **Read**: a trace (reading guide) does not exist yet. Writing one is itself a `trace` cycle. Once it exists, the **Semantic read** form takes signatures and refusals.
- **Anything else**: open a plain issue.

Rules and templates: https://github.com/Nervous-Machine/DEBRIEF/blob/main/CONTRIBUTING.md. Every contribution is one dated cycle under your own name and goes into `CITATION.cff` and the next release.

## Layout

```
ledger/erdos731.json   the ledger (protocol 0.1.0)
claim.yaml            the pinned claim this record was opened from
SCORECARD.md / ASKS.md  generated from the ledger
prereg_rerun.yaml     a pre-registration template for the first rerun (unregistered)
cycles/               contributed cycles, one file each
```

## Words

This record never calls the claim proved, verified or a theorem. It records what was claimed, what was checked by whom under what rule, and what is still open. Nothing here has standing until a cycle gives it one.
