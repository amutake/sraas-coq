Set Implicit Arguments.
Unset Strict Implicit.

Require Import configuration.

Parameter Ide : Set.

Inductive Actor (Id LS : Set) : Set :=
| actor' : Id -> LS -> Actor Id LS
| message' : Id -> LS -> Id -> Ide -> Actor Id LS.

Parameter LS0 : forall LS : Set, LS.
(* Arguments LS0 [LS]. *)

Definition actor {Id LS : Set} (id : Id) (ls : LS) := One (actor' id ls).
Definition message {Id LS : Set} (fr to : Id) (c : Ide) := One (message' fr (LS0 LS) to c).

(* The relation of actor name, configuration and the number of actors having the name *)
Inductive count {Id LS : Set} (id : Id) : Cfg (Actor Id LS) -> nat -> Prop :=
| count_empty : count id Null 0
| count_one : forall ls, count id (actor id ls) 1
| count_some_one : forall ls id', id <> id' -> count id (actor id' ls) 0
| count_ignore_message_one : forall fr ls to c, count id (One (message' fr ls to c)) 0
| count_more : forall s n ls, count id s n -> count id (s ++ (actor id ls)) (S n)
| count_some : forall s n ls id', count id s n -> id <> id' -> count id (s ++ (actor id' ls)) n
| count_ignore_message : forall s n fr ls to c, count id s n ->
                                             count id (s ++ One (message' fr ls to c)) n.

Definition mk_id_dec (Id : Set) :=
  forall id1 id2 : Id, { id1 = id2 } + { id1 <> id2 }.

Definition unique_ids {Id LS : Set} (s : Cfg (Actor Id LS)) : Prop :=
  forall id n, count id s n -> n <= 1.

Module Type ActorCfgTyp <: CfgTyp.
  Parameter Id : Set.
  Parameter LS : Set.
  Definition T := Actor Id LS.
  Definition t := Cfg T.
End ActorCfgTyp.

Module ActorCfgLemmas (P : ActorCfgTyp).

  Module ACAM := CfgAbelianMonoid P.
  Import P.
  Import ACAM.
  Module ACLemmas := CfgLemmas P.
  Import ACLemmas.

  Lemma count_equal : forall (id : Id) (s : Cfg (Actor Id LS)) n m,
                        count id s n ->
                        count id s m ->
                        n = m.
  Proof.
    intros id s n m.
    intros P.
    generalize dependent m.
    induction P; intros m Q;
    inversion Q; auto; subst; exfalso; auto.
  Qed.

  (* Lemma count_distr : forall (id : Id) (s1 s2 : Cfg (Actor Id LS)) n m l, *)
  (*                     mk_id_dec Id -> *)
  (*                     count id (s1 ++ s2) n -> *)
  (*                     count id s1 m -> *)
  (*                     count id s2 l -> *)
  (*                     n = m + l. *)
  (* Proof. *)
  (*   intros id s1 s2. *)
  (*   generalize dependent s1. *)
  (*   induction s2; *)
  (*     intros s1 n m l; *)
  (*     intros id_dec Cn Cm Cl; *)
  (*     unfold mk_id_dec in id_dec. *)

  (*   - inversion Cl; subst. *)
  (*     rewrite right_identity in Cn. *)
  (*     rewrite <- plus_n_O. *)
  (*     apply (count_equal Cn Cm). *)
  (*   - destruct t0. *)
  (*     + specialize (id_dec id i0). *)
  (*       destruct id_dec; subst. *)
  (*       * inversion Cl; subst; [ | exfalso; auto ]. *)
  (*         inversion Cn; subst; [ | exfalso; auto ]. *)
  (*         rewrite <- plus_n_Sm. *)
  (*         f_equal. *)
  (*         rewrite <- plus_n_O. *)
  (*         apply (count_equal H2 Cm). *)
  (*       * inversion Cl; subst; [ exfalso; auto | ]. *)
  (*         rewrite <- plus_n_O. *)
  (*         inversion Cn; subst; [ exfalso; auto | ]. *)
  (*         apply (count_equal H4 Cm). *)
  (*     + inversion Cl; inversion Cn; subst. *)
  (*       rewrite <- plus_n_O. *)
  (*       apply (count_equal H10 Cm). *)
  (*   - induction s2_2. *)
  (*     + rewrite right_identity in *. *)
  (*       apply (IHs2_1 s1 n m l id_dec Cn Cm Cl). *)
  (*     + destruct t0. *)
  (*       * assert (id_dec' : mk_id_dec Id); auto. *)
  (*         specialize (id_dec id i0). *)
  (*         destruct id_dec. *)
  (*         { *)
  (*           rewrite <- e in *. *)
  (*           inversion Cl; subst; [ | exfalso; auto ]. *)
  (*           rewrite <- associative in Cn. *)
  (*           inversion Cn; subst; [ | exfalso; auto ]. *)
  (*           rewrite <- plus_n_Sm. *)
  (*           f_equal. *)
  (*           eapply IHs2_1; auto. *)
  (*           apply H3. *)
  (*           apply Cm. *)
  (*         } *)
  (*         inversion Cl; subst; [ exfalso; auto | ]. *)
  (*         rewrite <- associative in Cn. *)
  (*         inversion Cn; subst; [ exfalso; auto | ]. *)
  (*         eapply IHs2_1; auto. *)
  (*         apply H5. *)
  (*         apply Cm. *)
  (*       * rewrite <- associative in Cn. *)
  (*         inversion Cn; inversion Cl; subst. *)
  (*         eapply IHs2_1 with s1; auto. *)
  (*     + Admitted. *)


  Lemma ignore_local_state : forall s n m (id id1 : Id) (ls1 ls2 : LS),
                               mk_id_dec Id ->
                               count id (s ++ actor id1 ls1) n ->
                               count id (s ++ actor id1 ls2) m ->
                               n = m.
  Proof.
    intros s n m id id1 ls1 ls2.
    intros id_dec C1 C2.
    unfold mk_id_dec in id_dec.
    specialize (id_dec id id1).
    destruct id_dec as [eq | neq].
    - rewrite eq in C1, C2.
      inversion C1; inversion C2; [ | exfalso; auto | exfalso; auto | exfalso; auto ]; subst.
      f_equal.
      apply (count_equal H2 H6).
    - inversion C1; inversion C2; subst; [ exfalso; auto | exfalso; auto | exfalso; auto | ].
      apply (count_equal H3 H9).
  Qed.

  Local Arguments Null : clear implicits.
  Lemma uids_empty : unique_ids (Null (Actor Id LS)).
  Proof.
    unfold unique_ids.
    intros id n H.
    inversion H.
    auto.
  Qed.
  Local Arguments Null [T].

  (* and more lemmas about unique_ids *)
End ActorCfgLemmas.
