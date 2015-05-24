Require Import Coq.Structures.Equalities.
Require Import algebra.

Inductive Cfg (T : Set) : Set :=
| Null : Cfg T
| One : T -> Cfg T
| Append : Cfg T -> Cfg T -> Cfg T.

Module Type CfgTypeParam.
  Parameter T : Set.
End CfgTypeParam.

Module Type CfgTyp <: Typ.
  Parameter T : Set.
  Definition t := Cfg T.
End CfgTyp.

(* Module CfgTyp (P : CfgTypeParam) <: Typ. *)
(*   Definition t := Cfg P.T. *)
(* End CfgTyp. *)

Module CfgMagma (P : CfgTyp) <: Magma P.
  Definition r := Append P.T.
End CfgMagma.

Module CfgIdentity (P : CfgTyp) <: Identity P.
  Definition i := Null P.T.
End CfgIdentity.

Module CfgAbelianMonoid (P : CfgTyp).
  Module PCM := CfgMagma P.
  Module PCI := CfgIdentity P.
  Module AM := AbelianMonoid P PCM PCI.
  Include P.
  Include PCM.
  Include PCI.
  Include AM.
End CfgAbelianMonoid.

Set Implicit Arguments.
Unset Strict Implicit.

Arguments Null [T].
Arguments One [T] _.
Arguments Append [T] _ _.

Notation "c ++ d" := (Append c d).

Inductive In {T : Set} (t : T) : Cfg T -> Prop :=
| InOne : In t (One t)
| InAppend : forall c d : Cfg T, In t c -> In t (c ++ d). (* defined only left pattern becase configuration is commutative *)

Hint Constructors In.

Module CfgLemmas (P : CfgTyp).

  Module C := CfgAbelianMonoid P.
  Import C.

  Lemma isolate1 : forall s (a : T),
                     In a s ->
                     exists s1, s = s1 ++ One a.
  Proof.
    intros s a P.
    induction P.
    - exists Null.
      rewrite left_identity.
      auto.
    - destruct IHP as [t H].
      exists (d ++ t).
      rewrite H.
      rewrite commutative.
      rewrite associative.
      auto.
  Qed.

  Lemma isolate2 : forall s (a : T),
                     (exists s1, s = s1 ++ One a) ->
                     In a s.
  Proof.
    intros s a P.
    destruct P as [t P].
    rewrite P.
    rewrite commutative.
    auto.
  Qed.

  Lemma Nonempty : forall (a : T) s1 s2,
                     In a (s1 ++ s2) <-> In a s1 \/ In a s2.
  Proof.
    intros a s1 s2.
    split; intros P.
    - inversion P; subst.
      left; auto.
    - destruct P as [P1 | P2].
      + auto.
      + rewrite commutative.
        auto.
  Qed.

  Goal forall s s1 s2 (a b : T),
         s = s1 ++ One a /\
         s = s2 ++ One b /\
         a <> b ->
         exists s3, s = s3 ++ One a ++ One b.
  Proof.
    intros s s1 s2 a b.
    intros P.
    destruct P as [P1 P'].
    destruct P' as [P2 P3].
    assert (In a s2 \/ In a (One b)).
    - eapply Nonempty.
      rewrite <- P2.
      eapply isolate2.
      exists s1; auto.
    - destruct H as [H | H].
      + assert (exists s3, s2 = s3 ++ One a).
        * apply isolate1; auto.
        * destruct H0 as [s3 H0].
          exists s3.
          rewrite P2.
          rewrite H0.
          rewrite associative.
          auto.
      + inversion H.
        contradiction.
  Qed.
End CfgLemmas.

(* - 次のゼミの準備ということもあるが、Structured Reasoning About Actor Systems の Athena による形式化を読んで、(理解するために) Coq で書きなおしてみている *)
(* - Actario の進捗はない *)
(*   - Configuration の定義はこれでいいのか (メッセージは必ず送られた順に起こる) <- 保証されない方向？ *)
(*   - アクターシステムの性質を記述するための言語 (ロジック、LTL とか) をどうするか (アクターシステムの性質記述に向いているものとは) <- PT-LTL (LTL の過去版 (Distributed 版は PT-DTL, Agha, Monitoring Oriented Programming)) *)
(*   - 分散システムをアクターで作る例から考えて、こういう性質を記述するためにこういう言語にしよう、とか証明を簡潔に記述していくための補題を作ろう、みたいな感じでやったら考えやすいのでは、SSReflect みたいに。 *)

(* - bounded buffer problem *)

(* - ABCL (メッセージの順番は保存される) *)
(* mpi *)

(* # JSSST *)

(* 1. Coq によるケーススタディを与える *)
(* 2. 型については、Agha は型と言っている、というだけでよいのでは。 *)
(* 3. 形式化は誰にとって嬉しいか？を明確にする *)
(* 4. pi計算をCoqで書いた他のものと比べてどういいのか *)

(* こっちは説明だけはちゃんと書こう。あとは Actario に注力しよう *)

(* # AGERE *)

(* Actario のほうは、Configuration の保たれる性質 *)
