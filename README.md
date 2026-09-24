# Flocq Atlas

A read-only, clickable map of the [Flocq](https://gitlab.inria.fr/flocq/flocq) floating-point library (pinned at 7aab8f55) and its Lean 4 port, [FloatSpec](https://github.com/Beneficial-AI-Foundation/FloatSpec) (Hantao Lou and contributors, BAIF). Lean links point at [Alok Singh's fork](https://github.com/alok/FloatSpec), which adds the source anchors and Rocq cross-checks this map is built from.

- Modules follow `coqdep -sort`; declarations follow Rocq's compiled `.glob` positions; solid edges come from coq-dpdgraph.
- **Definitions (roots)** is the default view: definitions are roots, and a theorem is folded into the declarations it depends on only when it is proven in the Lean snapshot and its compiled statement was spot-checked against pinned Flocq by Claude. Unproved or unchecked theorems stay visible.
- It is an exploration aid, not a proof certificate. Source matching is approximate; the code panes show the real hypotheses.

Live: https://alok.github.io/flocq-atlas/

Source excerpts keep their upstream licenses: Flocq (LGPL, `licenses/Flocq-LGPL.txt`) and FloatSpec (`licenses/FloatSpec-LICENSE.txt`).
