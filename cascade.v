From Coq Require Import List Lia Classical.
Import ListNotations.

Set Implicit Arguments.

Section Cascade.
  Variable C : Type.
  Variable zero : C -> Prop.
  Variable on_critical : C -> Prop.

  Definition off_critical (z : C) : Prop := zero z /\ ~ on_critical z.

  (* Cascade axiom: one off-critical zero yields arbitrarily many distinct off-critical zeros. *)
  Hypothesis cascade_many :
    (exists z, off_critical z) ->
    forall n : nat, exists l : list C,
      Forall off_critical l /\ NoDup l /\ length l = S n.

  (* Density axiom: there is a uniform finite bound on the number of distinct off-critical zeros. *)
  Hypothesis density_finite :
    exists N : nat, forall l : list C,
      Forall off_critical l -> NoDup l -> length l <= N.

  (* The cascade theorem: under the two hypotheses above, off-critical zeros cannot exist. *)
  Theorem cascade_theorem :
    ~ exists z, off_critical z.
  Proof.
    intros Hex.
    destruct density_finite as [N HN].
    pose proof (cascade_many Hex N) as [l [Hall [Hnd Hlen]]].
    specialize (HN l Hall Hnd).
    rewrite Hlen in HN.
    lia.
  Qed.

  (* Classical corollary: all zeros lie on the critical line. *)
  Corollary all_zeros_on_critical :
    forall z, zero z -> on_critical z.
  Proof.
    intros z Hz.
    destruct (classic (on_critical z)) as [H|H]; [assumption|].
    exfalso; apply cascade_theorem; exists z; split; [assumption|assumption].
  Qed.

End Cascade.
