Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import ZArith.
Require FMapList.
Require Import OrderedType OrderedTypeEx.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.Program.Tactics.
Import ListNotations.

(* BF Program Type *)
Inductive BF1 : Set :=
| bf_right (* > *)
| bf_left  (* < *)
| bf_inc   (* + *)
| bf_dec   (* - *)
| bf_out   (* . *)
| bf_in    (* , *)
| bf_loop : BF -> BF1  (* [...] *)
with
BF : Set :=
| bfz
| bfc : BF1 -> BF -> BF.

Scheme bf_mut := Induction for BF Sort Prop
with bf1_mut := Induction for BF1 Sort Prop.


Fixpoint bfapp bf1 bf2 :=
  match bf1 with
  | bfz => bf2
  | bfc b bf1' => bfc b (bfapp bf1' bf2)
  end.

Fixpoint bfrevc bf bf1 :=
  match bf with
  | bfz => bfc bf1 bfz
  | bfc b bf' => bfc b (bfrevc bf' bf1)
  end.

Lemma bfapp_bfz_l bf:
  bfapp bfz bf = bf.
  cbn; auto.
Qed.

Lemma bfapp_bfz_r bf:
  bfapp bf bfz = bf.
  induction bf; cbn; auto.
  now rewrite IHbf.
Qed.

Lemma bfapp_inv_r bf bf':
  bfapp bf bf' = bf -> bf' = bfz.
  induction bf; cbn; auto.
  intros; inversion H; now apply IHbf.
Qed.

Lemma bfapp_singleton_r bf bf1:
  bfapp bf (bfc bf1 bfz) = bfrevc bf bf1.
  induction bf; cbn; auto.
  now rewrite IHbf.
Qed.


Section StringFacts.
  Local Open Scope string.

  Lemma append_nil_r:
    forall s, s ++ "" = s.
  Proof.
    induction s; cbn; try rewrite IHs; auto.
  Qed.

  Lemma append_assoc:
    forall s1 s2 s3, s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
  Proof.
    induction s1; cbn; intros; auto.
    now rewrite IHs1.
  Qed.

  Lemma append_comm_cons:
    forall ch s1 s2, String ch (s1 ++ s2) = String ch s1 ++ s2.
  Proof.
    induction s1; cbn; intros; auto.
  Qed.

  Lemma append_length:
    forall s1 s2, length (s1 ++ s2) = length s1 + length s2.
  Proof.
    induction s1; cbn; auto.
  Qed.

  Lemma append_inv_ch_tail:
    forall s1 s2 ch, s1 ++ String ch "" = s2 ++ String ch "" ->
                     s1 = s2.
  Proof.
    induction s1; intros.
    destruct s2; simpl in H; auto.
    generalize (append_length (String a "") (s2 ++ String ch "")); intro L.
    replace (String a "" ++ s2 ++ String ch "") with (String a (s2 ++ String ch "")) in L by (now cbn).
    rewrite <- H in L.
    rewrite append_length in L.
    cbn in L; omega.

    simpl in H.
    destruct s2; simpl in H.
    destruct s1; simpl in H; inversion H.
    inversion H.
    apply IHs1 in H2.
    now rewrite H2.
  Qed.

  Lemma append_inv_tail:
    forall s1 s2 s, s1 ++ s = s2 ++ s -> s1 = s2.
  Proof.
    intros s1 s2 s; revert s1 s2; induction s; intros.
    now repeat rewrite append_nil_r in H.
    replace (String a s) with (String a EmptyString ++ s) in H by (now cbn).
    repeat rewrite append_assoc in H.
    apply IHs in H.
    now apply append_inv_ch_tail in H.
  Qed.

  Lemma append_tail:
    forall s1 s2 s, s1 = s2 -> s1 ++ s = s2 ++ s.
  Proof.
    intros; now subst.
  Qed.

  Lemma append_ch_nonempty:
    forall s1 ch s2, s1 ++ String ch s2 <> "".
  Proof.
    destruct s1; cbn; congruence.
  Qed.

  Lemma substring_empty:
    forall n s, substring n 0 s = ""%string.
  Proof.
    induction n; cbn.
    destruct s; auto.
    intros; destruct s; cbn; auto.
  Qed.

  Lemma substring_append:
    forall s1 s2, substring 0 (length s1) (s1 ++ s2) = s1.
  Proof.
    induction s1; cbn; intros.
    rewrite substring_empty; auto.
    now rewrite IHs1.
  Qed.

  Lemma substring_refl:
    forall s, substring 0 (length s) s = s.
  Proof.
    induction s; cbn; auto.
    now rewrite IHs.
  Qed.

  Lemma substring_length_1:
    forall s m, length (substring 0 m s) = min m (length s).
    induction s; induction m.
    1-3: now cbn.
    simpl; now rewrite IHs.
  Qed.

  Lemma substring_length:
    forall s n m, length (substring n m s) = min m (length s - n).
    induction s; induction n; induction m.
    1-5: now cbn.
    cbn; now rewrite substring_length_1.
    cbn; rewrite IHs; now cbn.
    cbn; rewrite IHs.
    remember (length s - n) as lsn; destruct lsn.
    now cbn.
    rewrite Nat.succ_min_distr; auto.
  Qed.

  Lemma substring_split:
    forall s n, n <= length s -> s = (substring 0 n s ++ substring n (length s - n) s).
  Proof.
    induction s; induction n; intros.
    rewrite substring_empty; now cbn.
    simpl in H; omega.
    rewrite substring_empty; simpl; rewrite substring_refl; now cbn.
    cbn; rewrite <- IHs; auto.
    cbn in H; omega.
  Qed.


  Fixpoint reverse s :=
    match s with
    | "" => s
    | String ch s => reverse s ++ (String ch "")
    end.

  Lemma reverse_app_distr:
    forall s1 s2, reverse (s1 ++ s2) = reverse s2 ++ reverse s1.
  Proof.
    induction s1; cbn; intros.
    now rewrite append_nil_r.
    rewrite IHs1; now rewrite append_assoc.
  Qed.

  Lemma reverse_involutive:
    forall s, reverse (reverse s) = s.
  Proof.
    induction s; cbn; auto.
    rewrite reverse_app_distr; cbn; now rewrite IHs.
  Qed.

  Lemma reverse_string_ind:
    forall P:string -> Prop,
      P ""%string ->
      (forall ch s, P (reverse s) -> P (reverse (String ch s))) ->
      forall s, P (reverse s).
  Proof.
    intros P Pn Papp s; induction s; auto.
  Qed.

  Lemma reverse_ind:
    forall P:string -> Prop,
      P ""%string ->
      (forall s ch, P s -> P (s ++ String ch ""))%string ->
      forall s, P s.
  Proof.
    intros P Pn Papp s.
    generalize (reverse_involutive s); intros E; rewrite <- E.
    apply reverse_string_ind; auto.
    intros; simpl; now apply Papp.
  Qed.


  Definition sconcat l := fold_right append ""%string l.

  Fixpoint sconcat_length ls :=
    match ls with
    | [] => 0
    | s :: ls => length s + sconcat_length ls
    end.

  Lemma sconcat_length_eq:
    forall ls, sconcat_length ls = length (sconcat ls).
  Proof.
    induction ls; cbn; auto.
    rewrite IHls; now rewrite append_length.
  Qed.

End StringFacts.

Section StringStrongInduction.

  Variable P:string -> Prop.
  Hypothesis IH: forall s, (forall t, length t < length s -> P t) -> P s.

  Local Lemma ssi_empty: P ""%string.
  Proof.
    apply IH. simpl. intros. omega.
  Qed.

  Local Lemma ssi_weak: forall s t, length t <= length s -> P t.
  Proof.
    induction s; intros.
    - simpl in H; destruct t; [apply ssi_empty | simpl in H; omega].
    - apply IH. intros. apply IHs. simpl in *. omega.
  Qed.
  
  Lemma string_strong_ind: forall s, P s.
  Proof.
    eauto using ssi_weak.
  Qed.

End StringStrongInduction.


Section StringNesting.

  (* [string_nest_check s] holds iff [s] is a properly nested string. *)
  Fixpoint string_nest_depth s n :=
    match s with
    | String ch s => if ascii_dec ch "["
                     then string_nest_depth s (S n)
                     else if ascii_dec ch "]"
                          then match n with
                               | S (S n) => string_nest_depth s (S n)
                               | _ => 0
                               end
                          else string_nest_depth s n
    | _ => n
    end.

  Definition string_nest_check s :=
    string_nest_depth s 1 = 1.

  Local Ltac nest_destruct :=
    match goal with
    | [ |- context [ string_nest_check _ ] ] => unfold string_nest_check
    | [ H : context [ string_nest_check _ ] |- _ ] => unfold string_nest_check in H
    | [ |- context [ string_nest_depth (String _ _) _ ] ] => cbn
    | [ H : context [ string_nest_depth (String _ _) _ ] |- _ ] => cbn in H
    | [ |- context [ string_nest_depth ""%string _ ] ] => cbn
    | [ H : context [ string_nest_depth ""%string _ ] |- _ ] => cbn in H
    | [ |- context [ string_nest_depth (append (String _ _) _) ] ] => rewrite <- append_comm_cons
    | [ |- context [ ascii_dec ?ch "[" ] ] => destruct (ascii_dec ch "[")
    | [ H : context [ ascii_dec ?ch "[" ] |- _ ] => destruct (ascii_dec ch "[")
    | [ |- context [ Nat.eq_dec ?n 0 ] ] => destruct (Nat.eq_dec n 0)
    | [ H : context [ Nat.eq_dec ?n 0 ] |- _ ] => destruct (Nat.eq_dec n 0)
    | [ |- context [ ascii_dec ?ch "]" ] ] => destruct (ascii_dec ch "]")
    | [ H : context [ ascii_dec ?ch "]" ] |- _ ] => destruct (ascii_dec ch "]")
    | [ H : ?ch = "["%char |- _ ] => rewrite H in *; clear H
    | [ H : ?ch = "]"%char |- _ ] => rewrite H in *; clear H
    | [ H : "["%char <> "["%char |- _ ] => congruence
    | [ H : "]"%char <> "]"%char |- _ ] => congruence
    end; try nest_destruct.

  Lemma string_nest_depth_append_nonzero s1 s2 n:
    string_nest_depth s1 n > 0 ->
    string_nest_depth (s1 ++ s2)%string n =
    string_nest_depth s2 (string_nest_depth s1 n).
  Proof.
    revert s2 n; induction s1; intros; nest_destruct; auto.
    destruct n as [|[|n]]; [ omega .. | auto ].
  Qed.

  Lemma string_nest_depth_add s n:
    string_nest_depth s n > 0 ->
    forall m, m >= n ->
              string_nest_depth s m =
              string_nest_depth s n + (m - n).
  Proof.
    revert n; induction s; intros; nest_destruct; auto.
    - omega.
    - replace (m - n) with (S m - S n) by omega.
      apply IHs; auto; omega.
    - destruct n as [|[|n]]; try omega.
      destruct m as [|[|m]]; try omega.
      replace (S (S m) - S (S n)) with (S m - S n) by omega.
      apply IHs; auto; omega.
  Qed.

  Lemma string_nest_check_tail s1 s2:
    string_nest_check s1 ->
    string_nest_check (s1 ++ s2)%string ->
    string_nest_check s2.
  Proof.
    intros; nest_destruct.
    rewrite string_nest_depth_append_nonzero in H0 by omega.
    now rewrite H in H0.
  Qed.

  Lemma string_nest_check_append s1 s2:
    string_nest_check s1 ->
    string_nest_check s2 ->
    string_nest_check (s1 ++ s2)%string.
  Proof.
    intros; nest_destruct.
    rewrite string_nest_depth_append_nonzero.
    now rewrite H.
    rewrite H; omega.
  Qed.

  Ltac nest_append_destruct :=
    match goal with
    | [ H : string_nest_depth ?s1 1 = 1
        |- context [string_nest_depth (append ?s1 ?s2) 2 = _] ] =>
      let HS := fresh H "_S" in
      assert (string_nest_depth s1 2 = 2) by
          (rewrite string_nest_depth_add with (n:=1); try rewrite H; omega);
      rewrite string_nest_depth_append_nonzero
    end; match goal with
         | [ H : string_nest_depth ?s1 2 = _
             |- context [string_nest_depth ?s1 2] ] => rewrite H; try nest_destruct; try omega
         end.

  Lemma string_nest_depth_break s n m:
    string_nest_depth s (S n) = S m ->
    m < n ->
    exists s1 s2, s = (s1 ++ String "]" s2)%string
                  /\ string_nest_depth s1 1 = 1
                  /\ string_nest_depth s2 n = S m.
  Proof.
    revert s n m.
    induction s using string_strong_ind; simpl; intros.

    destruct s; simpl in H0; [ omega | ].

    nest_destruct.
    - (* "[" case *)
      apply H in H0; [ | simpl; omega | omega ].
      destruct H0 as [s1 [s2 [A1 [A2 A3]]]].
      apply H in A3; [ | | omega ].
      destruct A3 as [t1 [t2 [B1 [B2 B3]]]].
      exists (String "[" (s1 ++ String "]" t1)), t2.
      split; [ | split ].
      + rewrite A1; rewrite B1; repeat rewrite append_comm_cons.
        now rewrite append_assoc.
      + nest_destruct.
        nest_append_destruct.
      + auto.
      + simpl; rewrite A1. rewrite append_length; simpl; omega.
    - (* "]" case *)
      destruct n; [ omega | ].
      exists ""%string, s; split; [ | split ]; auto.
    - (* everything else *)
      apply H in H0; auto.
      destruct H0 as [s1 [s2 [X0 [X1 X2]]]].
      subst; exists (String a s1), s2; split; [ | split ]; auto.
      now nest_destruct.
  Qed.

  Lemma string_nest_check_nest s:
    string_nest_check s ->
    string_nest_check (String "[" s ++ "]")%string.
  Proof.
    intros; nest_destruct.
    now nest_append_destruct.
  Qed.


  (* [string_nester s] shows inductively that [s] is nested. *)
  Inductive string_nester : string -> Prop :=
  | sn_empty : string_nester ""%string
  | sn_ch : forall ch s,
      ch <> "["%char ->
      ch <> "]"%char ->
      string_nester s ->
      string_nester (String ch s)
  | sn_nest : forall s1 s2,
      string_nester s1 ->
      string_nester s2 ->
      string_nester (String "[" s1 ++ String "]" s2)%string.
  Hint Constructors string_nester.

  Lemma string_nester_append s1 s2:
    string_nester s1 ->
    string_nester s2 ->
    string_nester (s1 ++ s2)%string.
  Proof.
    intros N1; revert s2; induction N1; intros; auto.
    apply IHN1 in H1; rewrite <- append_comm_cons; now constructor.
    apply IHN1_2 in H; rewrite <- append_assoc.
    replace (String "]" s2 ++ s0)%string with ("]" ++ s2 ++ s0)%string by (now simpl).
    apply sn_nest; auto.
  Qed.

  Lemma string_nester_checks s:
    string_nester s ->
    string_nest_check s.
  Proof.
    intros; induction H; unfold string_nest_check in *; cbn; auto.
    - now nest_destruct.
    - now nest_append_destruct.
  Qed.

  Lemma string_checks_nester s:
    string_nest_check s ->
    string_nester s.
  Proof.
    induction s using string_strong_ind; intros.
    destruct s; auto.
    nest_destruct.
    Local Ltac do_length := auto; simpl; repeat rewrite append_length; simpl; omega.
    - apply string_nest_depth_break in H0; [ | omega ].
      destruct H0 as [s1 [s2 [X0 [X1 X2]]]]; subst.
      apply H in X2; [ | do_length ].
      apply H in X1; [ | do_length ].
      rewrite append_comm_cons.
      now apply sn_nest.
    - discriminate.
    - auto.
  Qed.

  Lemma string_nester_iff:
    forall s, string_nest_check s <-> string_nester s.
  Proof.
    split; intros; [ apply string_checks_nester | apply string_nester_checks ]; auto.
  Qed.


  (* [string_prenest_check s] holds iff [s] starts with a left bracket,
     and [s] is a prefix of some properly nested string. *)
  Fixpoint string_prenest_depth s n :=
    match s with
    | ""%string => n
    | String ch s => if ascii_dec ch "["
                     then string_prenest_depth s (S n)
                     else if eq_nat_dec n 0
                          then n
                          else if ascii_dec ch "]"
                               then match n with
                                    | S (S n) => string_prenest_depth s (S n)
                                    | _ => 0
                                    end
                               else string_prenest_depth s n
    end.

  Definition string_prenest_check s :=
    string_prenest_depth s 0 > 0.

  Lemma string_prenest_depth_append_nonzero s1 s2 n:
    string_prenest_depth s1 n > 0 ->
    string_prenest_depth (s1 ++ s2) n =
    string_prenest_depth s2 (string_prenest_depth s1 n).
  Proof.
    revert s2 n; induction s1; cbn; intros; auto.
    nest_destruct.
    - now apply IHs1.
    - omega.
    - destruct n as [|[|n]]; [omega ..|].
      now apply IHs1.
    - now apply IHs1.
  Qed.

  Lemma string_prenest_depth_append_zero s1 s2 n:
    string_prenest_depth s1 n = 0 ->
    s1 = ""%string \/ string_prenest_depth (s1 ++ s2) n = 0.
  Proof.
    revert s2 n; induction s1 using reverse_ind; intros.
    now left.
    remember (string_prenest_depth s1 n) as N.
    destruct N; symmetry in HeqN.
    apply IHs1 with (s2:=String ch s2) in HeqN.
    destruct or HeqN.
    2: right; rewrite <- append_assoc; apply HeqN.
    all: right; rewrite <- append_assoc; rewrite <- append_comm_cons.
    2: rewrite string_prenest_depth_append_nonzero in * by (rewrite HeqN; omega).
    all: rewrite HeqN in *; clear HeqN.
    all: cbn in *.
    all: nest_destruct; auto.
    all: try discriminate.
    - destruct n as [|[|n]]; auto; discriminate.
    - congruence.
    - destruct N as [|[|N]]; auto; discriminate.
  Qed.

  Lemma string_prenest_depth_append_inv_nonzero s1 s2 n:
    string_prenest_depth (s1 ++ s2) n > 0 ->
    s1 = ""%string \/ string_prenest_depth s1 n > 0.
  Proof.
    revert s2 n; induction s1; intros.
    now left.
    remember (string_prenest_depth (String a s1) n) as N.
    destruct N; symmetry in HeqN.
    apply string_prenest_depth_append_zero with (s2:=s2) in HeqN.
    destruct or HeqN; [ discriminate | omega ].
    right; omega.
  Qed.

  Lemma string_prenest_depth_add s n:
    string_prenest_depth s n > 0 ->
    forall m, string_prenest_depth s (n + m) =
              string_prenest_depth s n + m.
  Proof.
    revert n; induction s; intros; cbn in *; auto.
    nest_destruct; auto; try omega.
    - rewrite <- plus_Sn_m; now apply IHs.
    - destruct n as [|[|n]]; try omega.
      repeat rewrite plus_Sn_m; rewrite <- plus_Sn_m; now apply IHs.
  Qed.

  Lemma string_prenest_depth_lbrack s:
    string_prenest_depth s 0 > 0 ->
    get 0 s = Some "["%char.
  Proof.
    induction s; intros; cbn in *.
    omega.
    destruct (ascii_dec a "["); [ subst; auto | omega ].
  Qed.


  (* Facts relating [string_prenest_check] and [string_nest_check] *)
  Lemma string_prenest_nest_eq_S:
    forall s n, string_prenest_depth s n > 0 ->
                string_nest_depth s (S n) = S (string_prenest_depth s n).
  Proof.
    induction s; intros; cbn in *; auto.
    nest_destruct; try omega.
    - now apply IHs.
    - destruct n as [|[|n]]; [omega .. | now apply IHs].
    - now apply IHs.
  Qed.

  Lemma string_prenest_nest_eq_1:
    forall s n, n > 0 ->
                string_prenest_depth s n = 1 ->
                string_nest_depth s n = 1.
  Proof.
    induction s; intros n NZ P.
    now cbn in *.
    simpl in P; nest_destruct; try omega; auto.
    destruct n as [|[|n]]; [discriminate .. |].
    apply IHs; [omega | auto].
  Qed.

  Lemma string_prenest_depth_add_rbrack s:
    string_prenest_depth s 0 = 1 ->
    string_nest_check (s ++ "]")%string.
  Proof.
    intros; unfold string_nest_check; cbn in *.
    assert (string_nest_depth s 1 = 2). {
      replace 2 with (S (string_prenest_depth s 0)) by omega.
      apply string_prenest_nest_eq_S; omega.
    }
    rewrite string_nest_depth_append_nonzero by omega.
    rewrite H0; cbn; omega.
  Qed.

  Lemma string_prenest_depth_nest_check s:
    string_prenest_depth s 1 = 1 ->
    string_nest_check s.
  Proof.
    intros; apply string_prenest_nest_eq_1; omega.
  Qed.

  Lemma string_prenest_depth_substring s:
    string_prenest_depth s 0 = 1 ->
    string_nest_check (substring 1 (length s - 1) s).
  Proof.
    intros; destruct s.
    cbn in H; congruence.
    assert (Some a = Some "["%char). {
      replace (Some a) with (get 0 (String a s)) by (cbn; auto).
      apply string_prenest_depth_lbrack.
      rewrite H; omega.
    }
    inversion H0; subst; clear H0.
    cbn in *.
    replace (length s - 0) with (length s) by omega.
    rewrite substring_refl.
    now apply string_prenest_depth_nest_check.
  Qed.

  Lemma string_prenest_depth_lt_nest_depth s n:
    string_nest_depth s (S n) > 0 ->
    string_prenest_depth s n < string_nest_depth s (S n).
  Proof.
    revert n; induction s; simpl; auto.
    intros; nest_destruct; auto.
    - destruct n; omega.
    - subst; auto.
    - destruct n as [|[|n]]; [omega .. |]; now apply IHs.
  Qed.


  (* Split a string into a list of strings with nested brackets.
     Handles improperly nested strings.
     e.g., "abc[def][" -> ["a"; "b"; "c"; "[def]"; "["]. *)

  Fixpoint split_nest' s n x :=
    match s with
    | ""%string => if string_dec x ""%string then [] else [x]
    | String ch s => if ascii_dec ch "["
                     then split_nest' s (S n) (x ++ "[")%string
                     else if ascii_dec ch "]"
                          then match n with
                               | 0 => (x ++ "]")%string :: split_nest' s n ""%string
                               | 1 => (x ++ "]")%string :: split_nest' s 0 ""%string
                               | S n => split_nest' s n (x ++ "]")%string
                               end
                          else match n with
                               | 0 => (x ++ String ch "")%string :: split_nest' s n ""%string
                               | S _ => split_nest' s n (x ++ String ch "")%string
                               end
    end.

  Definition split_nest s := split_nest' s 0 ""%string.

  Lemma split_nest'_sconcat:
    forall s n x, sconcat (split_nest' s n x) = (x ++ s)%string.
  Proof.
    induction s; cbn in *; intros.
    destruct (string_dec x ""); simpl; now rewrite append_nil_r.
    nest_destruct.
    - destruct n; rewrite IHs; now rewrite <- append_assoc.
    - destruct n as [|[|n]]; cbn; rewrite IHs; now rewrite <- append_assoc.
    - destruct n; cbn; rewrite IHs; rewrite <- append_assoc; cbn; auto.
  Qed.

  Lemma split_nest_sconcat:
    forall s, sconcat (split_nest s) = s.
  Proof.
    unfold split_nest; intros; now rewrite split_nest'_sconcat.
  Qed.


  (* This is the spec for [split_nest] when applied to correctly
     nested strings. *)
  Definition split_nest_element s :=
    match s with
    | ""%string =>
      (* no empty components *)
      False
    | String _ "" =>
      (* singleton components are nested (no brackets) *)
      string_nest_check s
    | String "[" sn =>
      (* if first char is a left bracket, then component is nested
         (ends with right bracket) and middle is nested (eliminates
         things like "[][]") *)
      string_nest_check s
      /\ string_nest_check (substring 0 (length sn - 1) sn)
    | _ => False
    end.

  Fixpoint split_nest_check ls :=
    match ls with
    | [] => True
    | s :: ls => split_nest_element s /\ split_nest_check ls
    end.

  Lemma split_nest_element_singleton ch:
    ch <> "["%char -> ch <> "]"%char -> split_nest_element (String ch "").
  Proof.
    intros; unfold split_nest_element; unfold string_nest_check.
    destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3; try solve [now cbn].
    all: destruct a4, a5, a6, a7; try solve [now cbn].
  Qed.


  (* If the input string is correctly nested,
     then the output of [split_nest] is correct. *)

  Lemma split_nest'_correct:
    forall s n x,
      (x = ""%string \/ n > 0) ->
      string_prenest_depth x 0 = n ->
      string_nest_check (x ++ s) ->
      split_nest_check (split_nest' s n x).
  Proof.
    induction s; intros n x P PN NC; destruct or P.
    - subst; now cbn.
    - simpl; destruct (string_dec x ""); cbn; try split; auto.
      rewrite append_nil_r in *.
      unfold string_nest_check in NC.
      assert (string_prenest_depth x 0 < 1). {
        rewrite <- NC; apply string_prenest_depth_lt_nest_depth; omega.
      }
      omega.
    - subst; cbn in *; nest_destruct.
      + apply IHs; [ right; omega | | ]; now cbn.
      + discriminate.
      + simpl. split; [apply split_nest_element_singleton|]; auto.
    - cbn in *; nest_destruct.
      + apply IHs.
        * right; omega.
        * rewrite string_prenest_depth_append_nonzero.
          all: rewrite PN; now simpl.
        * now rewrite <- append_assoc.
      + destruct n as [|[|n]]; [omega | |].
        assert (string_nest_check (x ++ "]")%string) as F. {
          now apply string_prenest_depth_add_rbrack.
        }
        * simpl; split; auto.
          destruct x; [simpl in PN; discriminate |].
          simpl in PN; destruct (ascii_dec a0 "["); [ subst | discriminate ].
          rewrite <- append_comm_cons.
          unfold split_nest_element.
          destruct x; simpl; [split; now cbn |].
          split.
          repeat rewrite append_comm_cons; auto.
          replace (length (x ++ "]") - 0) with (S (length x)) by (rewrite append_length; simpl; omega).
          rewrite substring_append.
          apply string_prenest_nest_eq_1; auto; omega.
          apply IHs; auto.
          simpl; apply string_nest_check_tail with (s1:=(x ++ "]")%string); auto.
          rewrite <- append_assoc; auto.
        * apply IHs; auto.
          right; omega.
          rewrite string_prenest_depth_append_nonzero.
          rewrite PN; now simpl.
          omega.
          rewrite <- append_assoc; auto.
      + destruct n; [omega|].
        apply IHs.
        right; omega.
        rewrite string_prenest_depth_append_nonzero.
        rewrite PN; simpl; nest_destruct; auto.
        omega.
        rewrite <- append_assoc; auto.
  Qed.

  Lemma split_nest_correct:
    forall s, string_nest_check s ->
              split_nest_check (split_nest s).
  Proof.
    intros; apply split_nest'_correct; [ left | cbn .. ]; auto.
  Qed.

  Lemma split_nest'_stash s1 s2 n x:
    string_nest_depth s1 (S n) > 0 ->
    split_nest' (s1 ++ s2)%string (S n) x =
    split_nest' s2 (string_nest_depth s1 (S n)) (x ++ s1)%string.
  Proof.
    revert s2 n x; induction s1; intros; nest_destruct.
    - now rewrite append_nil_r.
    - replace (x ++ String "[" s1)%string with ((x ++ "[") ++ s1)%string by (rewrite <- append_assoc; now simpl).
      now apply IHs1.
    - destruct n; [omega|].
      replace (x ++ String "]" s1)%string with ((x ++ "]") ++ s1)%string by (rewrite <- append_assoc; now simpl).
      now apply IHs1.
    - replace (x ++ String a s1)%string with ((x ++ String a "") ++ s1)%string by (rewrite <- append_assoc; now simpl).
      now apply IHs1.
  Qed.

  Lemma split_nest_append s1 s2:
    split_nest_element s1 ->
    split_nest (s1 ++ s2)%string = s1 :: split_nest s2.
  Proof.
    unfold split_nest_element; unfold split_nest; intros.
    destruct s1 as [s1 | ch s]; try contradiction.
    destruct s as [s | ch2 s]; try contradiction.
    all: destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
    all: destruct a0, a1, a2, a3; auto.
    1-2: destruct a4, a5, a6, a7; auto.
    all: unfold string_nest_check in *.
    1: cbn in H; discriminate.
    1-16: try contradiction.
    destruct a4, a5, a6, a7; try contradiction.
    destruct H as [H0 H1].
    assert (String ch2 s = substring 0 (length s) (String ch2 s) ++ substring (length s) 1 (String ch2 s))%string. {
      replace 1 with (length (String ch2 s) - length s).
      apply substring_split.
      simpl; try omega.
      simpl; destruct (length s); omega.
    }
    remember (substring 0 (length (String ch2 s) - 1) (String ch2 s)) as sp.
    remember (substring (length (String ch2 s) - 1) 1 (String ch2 s)) as sx.
    replace (length (String ch2 s) - 1) with (length s) in * by (cbn; omega).
    assert (length sx = 1). {
      rewrite Heqsx; rewrite substring_length.
      replace (length (String ch2 s) - length s) with 1.
      now simpl.
      simpl; destruct (length s); omega.
    }
    rewrite <- Heqsp in *; rewrite <- Heqsx in *; rewrite H in *.
    clear ch2 s Heqsp H Heqsx.
    cbn; rewrite <- append_assoc.
    rewrite split_nest'_stash.
    assert (sx = "]"%string). {
      destruct sx; [ simpl in H2; discriminate | ].
      destruct sx; [ | simpl in H2; discriminate ].
      simpl in H0.
      assert (string_nest_depth sp 2 = 2). {
        rewrite string_nest_depth_add with (n:=1); try rewrite H1; omega.
      }
      rewrite string_nest_depth_append_nonzero in H0.
      2: rewrite H; omega.
      rewrite H in H0; simpl in H0.
      destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
      destruct a0, a1, a2, a3; try discriminate.
      all: destruct a4, a5, a6, a7; try discriminate.
      auto.
    }
    rewrite H; simpl.
    now rewrite H1.
    rewrite H1; omega.
  Qed.

End StringNesting.

Section BFPrinting.

  Fixpoint unparse_bf1 (bf1:BF1) : string :=
    match bf1 with
    | bf_right => ">"
    | bf_left => "<"
    | bf_inc => "+"
    | bf_dec => "-"
    | bf_out => "."
    | bf_in => ","
    | bf_loop inner =>
      String "[" (unparse_bf inner) ++ "]"
    end
  with
    unparse_bf (bf:BF) : string :=
      match bf with
      | bfz => ""%string
      | bfc a bf' => append (unparse_bf1 a) (unparse_bf bf')
      end.

  Lemma unparse_bf_nest_check bf:
    string_nest_check (unparse_bf bf).
  Proof.
    induction bf using bf_mut
    with (P:=fun bf => string_nest_check (unparse_bf bf))
           (P0:=fun bf1 => string_nest_check (unparse_bf1 bf1)).
    all: unfold string_nest_check in *; try solve [cbn; auto].
    now apply string_nest_check_append.
    assert (string_nest_depth (unparse_bf bf) 2 = 2). {
      rewrite string_nest_depth_add with (n:=1); try rewrite IHbf; omega.
    }      
    simpl; fold unparse_bf.
    rewrite string_nest_depth_append_nonzero.
    now rewrite H.
    rewrite H; omega.
  Qed.

  Lemma unparse_bf1_nest_check bf1:
    string_nest_check (unparse_bf1 bf1).
  Proof.
    replace (unparse_bf1 bf1) with (unparse_bf (bfc bf1 bfz)).
    apply unparse_bf_nest_check.
    simpl; now rewrite append_nil_r.
  Qed.

  Lemma unparse_bf_empty bf:
    unparse_bf bf = ""%string -> bf = bfz.
  Proof.
    induction bf using bf_mut
    with (P:=fun bf => unparse_bf bf = ""%string -> bf = bfz)
           (P0:=fun bf1 => ~ unparse_bf1 bf1 = ""%string).
    all: intros; try solve [cbn; congruence].
    cbn in H.
    destruct b; discriminate.
  Qed.

  Lemma unparse_bfapp b1 b2:
    unparse_bf (bfapp b1 b2) = (unparse_bf b1 ++ unparse_bf b2)%string.
  Proof.
    induction b1; simpl; auto.
    rewrite IHb1; now rewrite append_assoc.
  Qed.
    
  Example print_all_bf_commands:
    unparse_bf
      (bfc (bf_loop
              (bfc bf_right (bfc bf_left (bfc bf_inc (bfc bf_dec
                                                          (bfc bf_out (bfc bf_in bfz)))))))
      bfz)
    = "[><+-.,]"%string. auto.
  Qed.

End BFPrinting.

Section BFParsing.

  Definition is_bfchar a :=
    match a with
    | ">" | "<" | "+" | "-" | "." | "," | "[" | "]" => true
    | _ => false
    end%char.

  Definition is_bfchar_nb a :=
    match a with
    | ">" | "<" | "+" | "-" | "." | "," => true
    | _ => false
    end%char.

  Fixpoint strip_nonbfchar s :=
    match s with
    | String ch s => if is_bfchar ch then String ch (strip_nonbfchar s) else strip_nonbfchar s
    | ""%string => s
    end.

  Definition parse_bf1 a bf :=
    match a with
    | ">" => bfc bf_right bf
    | "<" => bfc bf_left bf
    | "+" => bfc bf_inc bf
    | "-" => bfc bf_dec bf
    | "." => bfc bf_out bf
    | "," => bfc bf_in bf
    | _ => bf
    end%char.

  Function parse_split_bf (l:list string) {measure sconcat_length l} : BF :=
    match l with
    | [] => bfz
    | "" :: l => bfz
    | String ch "" :: l => parse_bf1 ch (parse_split_bf l)
    | (String "[" _) as s :: l =>
      let l2 := split_nest (substring 1 (length s - 2) s) in
      bfc (bf_loop (parse_split_bf l2)) (parse_split_bf l)
    | _ :: l => parse_split_bf l
    end%string.
  Proof.
    all: intros; try solve [cbn; omega].
    rewrite sconcat_length_eq; rewrite split_nest_sconcat.
    repeat rewrite <- teq10; cbn; rewrite substring_length_1.
    destruct (Nat.min_dec (length s0 - 1) (length s0)); rewrite e; omega.
  Defined.

  Definition parse_bf s :=
    parse_split_bf (split_nest s).

  Lemma parse_bf_append s1 s2:
    string_nest_check s1 ->
    parse_bf (s1 ++ s2)%string = bfapp (parse_bf s1) (parse_bf s2).
  Proof.
    intros NC.
    apply split_nest_correct in NC.
    remember (split_nest s1) as l.
    assert (s1 = sconcat l). {
      rewrite Heql; now rewrite split_nest_sconcat.
    }
    repeat rewrite H.
    clear s1 Heql H.

    revert s2; induction l; intros.
    - now simpl.
    - simpl in NC; destruct NC as [NC1 NC2].
      apply IHl with (s2:=s2) in NC2; clear IHl.
      simpl.
      rewrite <- append_assoc.

      unfold parse_bf in *.
      repeat rewrite (split_nest_append a); [ | auto | auto].
      rewrite parse_split_bf_equation with (l:=a :: split_nest (sconcat l ++ s2)).
      rewrite parse_split_bf_equation with (l:=a :: split_nest (sconcat l)).
      rewrite NC2.
      remember (parse_split_bf (split_nest (sconcat l))) as P.
      remember (parse_split_bf (split_nest s2)) as Q.

      destruct a as [s | ch s]; try contradiction.
      destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
      destruct s; try contradiction.
      all: destruct a0, a1, a2, a3; auto.
      all: destruct a4, a5, a6, a7; auto.
  Qed.

  Lemma parse_bf_inverse b:
    parse_bf (unparse_bf b) = b.
  Proof.
    induction b using bf_mut with
    (P:=fun b => parse_bf (unparse_bf b) = b)
      (P0:=fun b => parse_bf (unparse_bf1 b) = bfc b bfz).
    1, 3-8: cbn; auto.

    simpl.
    rewrite parse_bf_append.
    rewrite IHb; rewrite IHb0; now cbn.
    apply unparse_bf1_nest_check.

    simpl.
    unfold parse_bf; unfold split_nest.
    cbn.
    rewrite split_nest'_stash by (rewrite unparse_bf_nest_check; auto).
    rewrite unparse_bf_nest_check.
    cbn.
    rewrite parse_split_bf_equation.
    remember (unparse_bf b ++ "]")%string as bb.
    assert (exists ch bbp, bb = String ch bbp). {
      destruct bb.
      destruct (unparse_bf b); simpl in Heqbb; discriminate.
      eauto.
    }
    destruct H as [ch [bbp H]]; rewrite H.
    replace (length (String "[" (String ch bbp)) - 2) with (length bbp).
    replace (substring 1 (length bbp) (String "[" (String ch bbp))) with (unparse_bf b).
    unfold parse_bf in IHb; rewrite IHb.
    auto.
    rewrite <- H; simpl.
    rewrite Heqbb.
    replace (length bbp) with (length (unparse_bf b)).
    now rewrite substring_append.
    replace (length (unparse_bf b)) with (length (unparse_bf b) + length "]" - length "]")%string.
    rewrite <- append_length.
    rewrite <- Heqbb.
    rewrite H.
    simpl; omega.
    simpl; omega.
    simpl; omega.
  Qed.

  Lemma strip_nonbfchar_append s1 s2:
    strip_nonbfchar (s1 ++ s2)%string = (strip_nonbfchar s1 ++ strip_nonbfchar s2)%string.
  Proof.
    induction s1; cbn; auto.
    destruct (is_bfchar a).
    rewrite <- append_comm_cons; rewrite IHs1; auto.
    auto.
  Qed.

  Lemma unparse_bf_inverse s:
    string_nest_check s ->
    unparse_bf (parse_bf s) = strip_nonbfchar s.
  Proof.
    intros SN.
    rewrite string_nester_iff in SN.
    induction SN.
    - now cbn.
    - assert (string_nester (String ch "")) as SN1. {
        constructor; auto; constructor.
      }
      rewrite <- string_nester_iff in SN1.
      replace (String ch s) with (String ch "" ++ s)%string by (now cbn).
      rewrite parse_bf_append; auto.
      rewrite unparse_bfapp.
      rewrite IHSN.
      rewrite strip_nonbfchar_append.
      apply append_tail.

      destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
      destruct a0, a1, a2, a3; cbn; auto.
      all: destruct a4, a5, a6, a7; cbn; auto.
      all: discriminate.
    - replace (String "]" s2) with ("]" ++ s2)%string by (now cbn).
      rewrite append_assoc.
      rewrite parse_bf_append.
      2: apply string_nester_checks; apply sn_nest; auto; apply sn_empty.
      rewrite unparse_bfapp.
      rewrite IHSN2.
      rewrite strip_nonbfchar_append.
      apply append_tail.

      assert (split_nest_element (String "[" s1 ++ String "]" "")). {
        destruct s1; cbn.
        split; unfold string_nest_check; cbn; auto.
        replace (length (s1 ++ "]") - 0)%string with (S (length s1)) by (rewrite append_length; simpl; omega).
        rewrite substring_append.
        rewrite <- string_nester_iff in SN1.
        split; auto.
        repeat rewrite append_comm_cons.
        now apply string_nest_check_nest.
      }

      unfold parse_bf.
      replace "]"%string with ("]" ++ "")%string at 1 by (now cbn).
      rewrite append_assoc.
      rewrite split_nest_append; auto.
      unfold split_nest; simpl split_nest'.
      rewrite parse_split_bf_equation.
      rewrite <- append_comm_cons.
      remember (s1 ++ "]")%string as s1x; destruct s1x.
      destruct s1; discriminate.
      remember (substring 1 (length (String "[" (String a s1x)) - 2) (String "[" (String a s1x))) as s1y.
      rewrite Heqs1x in *; clear s1x Heqs1x.
      simpl in Heqs1y.
      replace (length (s1 ++ "]")%string - 1) with (length s1) in Heqs1y by (rewrite append_length; simpl; omega).
      rewrite substring_append in Heqs1y.
      rewrite Heqs1y.
      unfold unparse_bf; fold unparse_bf.
      unfold parse_bf in IHSN1; rewrite IHSN1.
      rewrite parse_split_bf_equation; simpl.
      rewrite append_nil_r.
      rewrite strip_nonbfchar_append; now simpl.
  Qed.


  Example parse_all_bf_commands:
    parse_bf "[><+-.,]" =
    bfc (bf_loop
           (bfc bf_right (bfc bf_left (bfc bf_inc (bfc bf_dec (bfc bf_out (bfc bf_in bfz))))))) bfz.
  now cbn. Qed.

  Example parse_nesting_bf:
    parse_bf "[[[][]]][]" =
    bfc
      (bf_loop (bfc
                  (bf_loop (bfc
                              (bf_loop bfz)
                              (bfc (bf_loop bfz) bfz))) bfz))
      (bfc (bf_loop bfz) bfz).
  now cbn. Qed.

  Example parse_empty_bf:
    parse_bf EmptyString = bfz.
  now cbn. Qed.

  Example parse_bf_bad_left:
    parse_bf "[[]" = bfc (bf_loop bfz) bfz.
  now cbn. Qed.

  Example parse_bf_bad_right:
    parse_bf "[]]" = bfc (bf_loop bfz) bfz.
  now cbn. Qed.

End BFParsing.



(* BF Interpreter *)
(* A BFTape is a map from [nat] indices to [Z] values *)
Module NatMap := FMapList.Make Nat_as_OT.
Definition BFTape := NatMap.t Z.

Definition tape_get (tape: BFTape) (ptr: nat): Z :=
  match (NatMap.find ptr tape) with
  | Some x => x
  | None => 0
  end.

Definition tape_set (tape: BFTape) (ptr: nat) (x: Z): BFTape :=
  NatMap.add ptr x tape.

Definition tape_inc (tape: BFTape) (ptr: nat): BFTape :=
  tape_set tape ptr (Z.succ (tape_get tape ptr)).

Definition tape_dec (tape: BFTape) (ptr: nat): BFTape :=
  tape_set tape ptr (Z.pred (tape_get tape ptr)).

(* `bf' is the current state of the program, while `resets' is the
stack of programs to reset to at the end of a loop *)
(* TODO: Generalize to all tape languages *)
Inductive BFState : Type :=
  bf_state (bf: BF)
           (resets: list BF)
           (ptr: nat)
           (tape: BFTape)
           (input: list Z)
           (output: list Z).

Function state_init (bf: BF) (input: list Z): BFState :=
  bf_state bf [] 0 (NatMap.empty Z) input [].

Function state_output (state: BFState): list Z :=
  match state with bf_state _ _ _ _ _ output => output end.

Function bf_step (state: BFState): option BFState :=
  match state with
  | bf_state bf resets ptr tape input output =>
    match bf with
     | bf_end =>
       match resets with
        | [] => None
        | bf' :: resets' =>
          Some (bf_state bf' resets' ptr tape input output)
        end
     | bf_right bf' =>
       Some (bf_state bf' resets (S ptr) tape input output)
     | bf_left bf' =>
       Some (bf_state bf' resets (pred ptr) tape input output)
     | bf_inc bf' =>
       Some (bf_state bf' resets ptr (tape_inc tape ptr) input output)
     | bf_dec bf' =>
       Some (bf_state bf' resets ptr (tape_dec tape ptr) input output)
     | bf_out bf' =>
       Some (bf_state bf' resets ptr tape input (output ++ [tape_get tape ptr]))
     | bf_in bf' =>
       match input with
        | [] =>
          Some (bf_state bf' resets ptr (tape_set tape ptr 0) input output)
        | x :: input' =>
          Some (bf_state bf' resets ptr (tape_set tape ptr x) input' output)
        end
     | bf_loop inner_bf bf' =>
       if Z.eqb (tape_get tape ptr) Z.zero then
         Some (bf_state bf' resets ptr tape input output)
       else
          Some (bf_state inner_bf (bf :: resets) ptr tape input output)
     end
  end.

(* TODO: Use N as fuel with {measure N.to_nat fuel} *)
Function bf_run (state: BFState) (fuel: nat): option (list Z) :=
  match fuel with
  | 0 => None
  | S f =>
    match bf_step state with
    | None => Some (state_output state)
    | Some state' => bf_run state' f
    end
  end.

Function z_of_ascii (a: ascii): Z :=
  Z.of_nat (nat_of_ascii a).

Function ascii_of_z (z: Z): option ascii :=
  match z with
  | Zpos p => Some (ascii_of_pos p)
  | _ => None
  end.

Function opt_list_len {A: Type} (l: option (list A)): nat :=
  match l with
  | Some l => List.length l
  | None => 0
  end.

Function string_of_zs (out: list Z): string :=
  match out with
  | [] => EmptyString
  | z :: zs' =>
    match ascii_of_z z with
    | None => EmptyString
    | Some a => String a (string_of_zs zs')
    end
  end.

Function zs_of_string (str: string): list Z :=
  match str with
  | EmptyString => []
  | String a str' => z_of_ascii a :: (zs_of_string str')
  end.

(* The important interpreter as far as the spec is concerned *)
Function interpret_bf (prog: string) (zs: list Z) (f: nat): option (list Z) :=
  match parse_bf prog with
  | None => None
  | Some bf => bf_run (state_init bf zs) f
  end.

Function interpret_bf_readable (prog: string) (input: string) (f:nat): string :=
  match interpret_bf prog (zs_of_string input) f with
  | None => EmptyString
  | Some zs => string_of_zs zs
  end.

Example hello_world_bf:
  interpret_bf_readable "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.
                        +++++++..+++.>++.<<+++++++++++++++.>.+++.------.
                        --------.>+. newline in next cell" "" 399 =
  "Hello World!"%string. auto.
