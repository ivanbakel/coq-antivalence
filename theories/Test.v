From Antivalence Require Import Loader.

Axiomatize Type Inequality.

Hint Resolve bool_neq_nat : core.

Theorem nat_is_not_bool : nat <> bool.
Proof.
  auto.
  Qed.

