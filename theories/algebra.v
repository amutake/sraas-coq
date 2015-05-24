Require Import Coq.Structures.Equalities.

Module Type Magma (Import T : Typ).
  Parameter Inline r : t -> t -> t.
  Infix "+" := r.
End Magma.

Module Semigroup (T : Typ) (Import M : Magma T).
  Axiom associative : forall x y z, (x + y) + z = x + (y + z).
End Semigroup.

Module Type Identity (Import T : Typ).
  Parameter Inline i : t.
End Identity.

Module IdentityAxioms (T : Typ) (Import M : Magma T) (Import I : Identity T).
  Axiom left_identity : forall x, i + x = x.
  Axiom right_identity : forall x, x + i = x.
End IdentityAxioms.

Module Monoid (T : Typ) (M : Magma T) (I : Identity T) :=
  Semigroup T M <+ IdentityAxioms T M I.

Module Commutativity (T : Typ) (Import M : Magma T).
  Axiom commutative : forall x y, x + y = y + x.
End Commutativity.

Module AbelianMonoid (T : Typ) (M : Magma T) (I : Identity T) :=
  Monoid T M I <+ Commutativity T M.
