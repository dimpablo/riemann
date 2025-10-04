From Coq Require Import List Lia Classical.
Import ListNotations.

Require Import cascade.

Module ToyModel.
  (* We instantiate the abstract schema with a simple finite carrier to test logic. *)
  Inductive Point := a | b | c.

  Definition zero (_ : Point) : Prop := True.
  Definition on_critical (p : Point) : Prop :=
    match p with a => True | _ => False end.

  (* Define the off-critical predicate inline; it is definally equal to
     the library's [off_critical] specialized to this instance. *)
  Definition offc (p : Point) : Prop := zero p /\ ~ on_critical p.

  (* Provide axioms mimicking the cascade and density with contradictory bounds to trigger the theorem. *)
  Axiom cascade_many :
    (exists z : Point, offc z) ->
    forall n : nat, exists l : list Point,
      Forall offc l /\ NoDup l /\ length l = S n.

  Axiom density_finite :
    exists N : nat, forall l : list Point,
      Forall offc l -> NoDup l -> length l <= N.

  (* Reuse the generic theorem by specializing its parameters. *)
  Lemma toy_no_offcritical : ~ exists z : Point, offc z.
  Proof.
    eapply (cascade.cascade_theorem (C:=Point) (zero:=zero) (on_critical:=on_critical));
      [exact cascade_many | exact density_finite].
  Qed.

  (* Also check the classical corollary compiles and specializes. *)
  Lemma all_on_critical_from_axioms : forall z, zero z -> on_critical z.
  Proof.
    intros z Hz.
    refine (cascade.all_zeros_on_critical
              (C:=Point) (zero:=zero) (on_critical:=on_critical)
              cascade_many density_finite z Hz).
  Qed.

End ToyModel.
