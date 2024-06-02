From Lab11 Require Import ulc.

(* Check ulc.v for the definition of `step`. *)

Definition True := <{ λ x . λ y . x  }>.
Definition False := <{ λ x . λ y . y  }>.
Definition IF := <{ λ b . λ t . λ f . b t f }>.
Definition AND := <{ λ p . λ q. p q p }>.

Example multistep_1 : forall c1 c2,
  <{ IF True c1 c2 }> -->* c1.
Proof.
  intros.
  unfold IF, True.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_AppAbs.
  simpl. eapply multi_step.
    admit.
    apply multi_refl.
Admitted.

Example multistep_2 : forall c1 c2,
  <{ IF False c1 c2 }> -->* c2.
Proof.
  intros.
  unfold IF, False.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_AppAbs.
  simpl. apply multi_refl.
Qed.

Example multistep_3 :
  <{ AND True False }> -->* False.
Proof.
  unfold AND, True, False.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_App1. apply ST_AppAbs.
  simpl. eapply multi_step.
    apply ST_AppAbs.
  simpl. apply multi_refl.
Qed.