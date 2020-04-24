# Antivalence - a Coq plugin to generate type inequality axioms

Coq's underlying logical system (the calculus of inductive constructions) is compatible with the axiom of univalence - that isomorphic types are equal. Unfortunately, this means that statements that would otherwise seem obvious, such as `nat <> string`, are unprovable. In fact, the only type inequalities that are provable in Coq are those for types which have different cardinalities, such as `nat <> bool`.

Since CIC is consistent with univalence, it is also consistent with its negation - so it is also possible to consistently introduce axioms that state that distinct inductive types are not equal. That's the goal of `Antivalence`.

## Vernacular command

This plugin adds a single new vernacular command to Coq - `Axiomatize Type Inequality.` This command defines a single axiom `<ind1>_neq_<ind2>` for each pair of inductive types in the environment (no reordered pairs), which `forall` quantifies all the type parameters of each type and states that they are not equal.

For example, for `list` and `prod, the axiom generated is
```
Axiom list_neq_sum : forall A A0 B : Type, list A <> sum A0 B.
```
