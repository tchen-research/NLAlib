# Targeting guide

Use this guide to choose and formulate work for the RandNLA library. The atlas is a catalogue and
dependency map; it is useful for finding open results, existing formalizations, and downstream
users, but it does not prescribe which results may be worked on or require a catalogue entry for
every helper.

## Choosing a target

Start with the intended mathematical or computational use. Check the atlas and current Lean API
for existing results and dependencies, then choose a concrete improvement: a missing theorem, a
clearer statement, a useful bridge, or a connection between a specification and an algorithm.
Downstream reuse can help prioritize work, but a short isolated result or a practical API gap is
also a reasonable target.

Before defining an object, search Mathlib and this library. Reuse Mathlib's object where it has the
right meaning; otherwise introduce a recognizable mathematical object and give users useful
constructors, elimination lemmas, and bridges to standard interfaces.

## Designing statements

The statement should preserve the mathematics and serve the intended use. Read the cited result
and identify its hypotheses, domains, dimensions, constants, failure modes, and degenerate cases
before settling on a Lean representation. Do not weaken a result merely to make its proof easier.

Use finite index types where appropriate. Generalize across fields, index types, or probability
spaces when that is mathematically valid and improves reuse. `Fin` is suitable when its order,
recursion, or dimension structure is part of an algorithm or proof. Existential constants and
asymptotic statements are valid when they match the source or the intended result; expose explicit
constants when they are part of the theorem or add useful precision.

For probabilistic results, make the law or distributional assumptions clear. Prefer `HasLaw`,
actual measures, and measure-theoretic expectations when they are natural for the application.
Finite sums, PMFs, and specialized measures are also useful interfaces; add bridges to the
corresponding probability law or expectation where needed.

Keep a specification distinct from a claim about a particular algorithm. An algorithm guarantee
needs a proved connection between its implementation or process and the specification it uses.
State which dimensions, breakdown cases, and costs are covered by the guarantee.

Use Mathlib's standard order, norm, probability, and functional-calculus objects where they fit.
Name and document adapters that resolve genuine differences in representation. Bundled seminorms
and similar structures are appropriate when they enable generic API reuse; connect them to the
underlying scalar definition with evaluation lemmas.

## Proving and recording work

Search Mathlib and the local library before proving a fact. Prefer a direct proof from established
results, with explicit hypotheses and no new axioms. If a substantial proof is deferred, put it in
a named, documented scaffold and record its trust status accurately. Never let a scaffold or
assumption silently change the meaning of a downstream statement.

Give public declarations useful mathematical names and document their source and statement. Add an
atlas entry and `atlas:` tag when formalizing a catalogued research result; ordinary helper lemmas,
bridges, and API contributions do not need a bespoke atlas entry. Keep atlas dependencies and
status synchronized when a catalogued result changes.

Use [`../docs/STANDARDS.md`](../docs/STANDARDS.md) for current naming, organization, and statement
conventions, and [`../CONTRIBUTING.md`](../CONTRIBUTING.md) for the repository workflow.
