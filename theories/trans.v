Set Implicit Arguments.
Unset Strict Implicit.

Require Import configuration actor.

Inductive Step (Id : Set) :=
| receive : Id -> Id -> Ide -> Step Id
| send : Id -> Id -> Ide -> Step Id
| create : Id -> Id -> Step Id.

Inductive TP (Id LS : Set) :=
| Initial : TP Id LS
| then' : TP Id LS -> Step Id -> TP Id LS.

Notation "tp 'then' step" := (then' tp step)  (at level 0).

Parameter config : forall Id LS : Set, TP Id LS -> Cfg (Actor Id LS).
Axiom ready_to : forall Id LS : Set, LS -> Step Id -> Prop. (* ? *)
Parameter next : forall Id LS : Set, LS -> Step Id -> LS.
Parameter new_ls : forall LS : Set, LS -> LS.

Inductive before {Id LS : Set} (T : TP Id LS) (s : Cfg (Actor Id LS)) (ls : LS) : Step Id -> Prop :=
| before_receiving : forall id fr c,
                       config T = s ++ (actor id ls) ++ (message fr id c) ->
                       ready_to ls (receive id fr c) ->
                       before T s ls (receive id fr c)
| before_sending : forall id to c,
                     config T = s ++ (actor id ls) ->
                     ready_to ls (send id to c) ->
                     before T s ls (send id to c)
| before_creating : forall id id',
                      config T = s ++ (actor id ls) ->
                      unique_ids ((config T) ++ (actor id' (new_ls ls))) ->
                      ready_to ls (create id id') ->
                      before T s ls (create id id').

Inductive after {Id LS : Set} (T : TP Id LS) (s : Cfg (Actor Id LS)) (ls : LS) : Step Id -> Prop :=
| after_receiving : forall id fr c,
                      config (T then (receive id fr c)) =
                      s ++ (actor id (next ls (receive id fr c))) ->
                      after T s ls (receive id fr c)
| after_sending : forall id to c,
                    config (T then (send id to c)) =
                    s ++ (actor id (next ls (send id to c))) ++ (message id to c) ->
                    after T s ls (send id to c)
| after_creating : forall id id',
                     config (T then (create id id')) =
                     s ++ (actor id (next ls (create id id'))) ++ (actor id' (new_ls ls)) ->
                     after T s ls (create id id').

Local Arguments before : clear implicits.
Local Arguments after : clear implicits.
Axiom transition_step : forall Id LS T s ls step,
                          before Id LS T s ls step ->
                          after Id LS T s ls step.

Lemma trans_receive : forall Id LS T (id : Id) s (ls : LS) fr c,
                        config T = s ++
                                     (actor id ls) ++
                                     (message fr id c) /\
                        ready_to ls (receive id fr c) ->
                        config (then' T (receive id fr c)) =
                        s ++ (actor id (next ls (receive id fr c))).
Proof.
