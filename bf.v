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


  Lemma append_get:
    forall s n ch, get n s = Some ch ->
                   forall s', get n (s ++ s')%string = Some ch.
  Proof.
    intros s n; revert s; induction n; intros.
    destruct s; cbn in *; try discriminate; auto.
    destruct s; cbn in *; try discriminate; now apply IHn.
  Qed.

  Lemma get_append_tail:
    forall s ch, get (length (s ++ String ch "") - 1) (s ++ String ch "") = Some ch.
  Proof.
    induction s; cbn; auto.
    intros; rewrite append_length; simpl.
    replace (length s + 1 - 0) with (S (length s)) by omega.
    replace (length s) with (length (s ++ String ch "") - 1) by (rewrite append_length; simpl; omega).
    apply IHs.
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


Section StringNesting.

  (* Split a string into a list of strings with nested brackets.
     Handles improperly nested strings.
     e.g., "abc[def][" -> ["a"; "b"; "c"; "[def]"; "["]. *)
  
  Function split_nest' s n x :=
    match s, n with
    | String "[" s, 0 => split_nest' s 1 (x ++ "[")%string
    | String "[" s, S _ => split_nest' s (S n) (x ++ "[")%string
    | String "]" s, 1 => (x ++ "]")%string :: split_nest' s 0 ""%string
    | String "]" s, S n => split_nest' s n (x ++ "]")%string
    | String ch s, 0 => (x ++ String ch "")%string :: split_nest' s n ""%string
    | String ch s, S _ => split_nest' s n (x ++ String ch "")%string
    | ""%string, _ => if string_dec x ""%string then [] else [x]
    end.

  Definition split_nest s := split_nest' s 0 ""%string.

  Lemma split_nest'_sconcat:
    forall s n x, sconcat (split_nest' s n x) = (x ++ s)%string.
    intros s n x; functional induction (split_nest' s n x).
    1, 2, 4, 6: rewrite IHl; now rewrite <- append_assoc.
    1, 2: simpl; rewrite IHl; now rewrite <- append_assoc.
    1, 2: now simpl.
  Qed.

  Lemma split_nest_sconcat:
    forall s, sconcat (split_nest s) = s.
    unfold split_nest; intros; now rewrite split_nest'_sconcat.
  Qed.


  (* [string_nest_check s] holds iff [s] is a properly nested string. *)
  Fixpoint string_nest_check' s n :=
    match s, n with
    | String "[" s, _ => string_nest_check' s (S n)
    | String "]" s, S (S n) => string_nest_check' s (S n)
    | String "]" s, _ => 0
    | String ch s, _ => string_nest_check' s n
    | ""%string, _ => n
    end.

  Definition string_nest_check s := string_nest_check' s 1 = 1.

  Lemma string_nest_check'_append_nonzero s1 s2 n:
    string_nest_check' s1 n > 0 ->
    string_nest_check' (s1 ++ s2)%string n =
    string_nest_check' s2 (string_nest_check' s1 n).
  Proof.
    revert s2 n; induction s1; intros.
    cbn; auto.
    cbn in *.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [now apply IHs1].
    all: destruct a4, a5, a6, a7.
    all: try solve [now apply IHs1].
    destruct n; [ | destruct n ]; try omega.
    now apply IHs1.
  Qed.

  Lemma string_nest_check'_add s n:
    string_nest_check' s n > 0 ->
    forall m, string_nest_check' s (n + m) =
              string_nest_check' s n + m.
  Proof.
    revert n; induction s; intros.
    cbn; auto.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [ cbn in *; now apply IHs ].
    all: destruct a4, a5, a6, a7.
    all: try solve [ cbn in *; now apply IHs ].
    cbn in *; rewrite <- plus_Sn_m. now apply IHs.
    cbn in *; destruct n; [ omega | destruct n ]; [ omega | ].
    repeat rewrite plus_Sn_m; rewrite <- plus_Sn_m.
    now apply IHs.
  Qed.

  Lemma string_nest_check_tail s1 s2:
    string_nest_check s1 ->
    string_nest_check (s1 ++ s2)%string ->
    string_nest_check s2.
  Proof.
    intros; unfold string_nest_check in *.
    rewrite string_nest_check'_append_nonzero in H0 by omega.
    now rewrite H in H0.
  Qed.


  (* [string_prenest_check s] holds iff [s] starts with a left bracket,
     and [s] is a prefix of some properly nested string. *)
  Fixpoint string_prenest_check' s n :=
    match s, n with
    | ""%string, _ => n
    | String "[" s, _ => string_prenest_check' s (S n)
    | _, 0 => n
    | String "]" s, S (S n) => string_prenest_check' s (S n)
    | String "]" s, S _ => 0
    | String ch s, S _ => string_prenest_check' s n
    end.

  Definition string_prenest_check s :=
    string_prenest_check' s 0 > 0.

  Lemma string_prenest_check'_append_nonzero s1 s2 n:
    string_prenest_check' s1 n > 0 ->
    string_prenest_check' (s1 ++ s2) n =
    string_prenest_check' s2 (string_prenest_check' s1 n).
  Proof.
    revert s2 n; induction s1; cbn; intros.
    destruct n; omega.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [destruct n; [ omega | now apply IHs1 ]].
    all: destruct a4, a5, a6, a7.
    all: try solve [destruct n; [ omega | now apply IHs1 ]].
    now apply IHs1.
    destruct n; try omega.
    destruct n; try omega.
    now apply IHs1.
  Qed.

  Lemma string_prenest_check'_append_zero s1 s2 n:
    string_prenest_check' s1 n = 0 ->
    s1 = ""%string \/ string_prenest_check' (s1 ++ s2) n = 0.
  Proof.
    revert s2 n; induction s1 using reverse_ind; intros.
    now left.
    remember (string_prenest_check' s1 n) as N.
    destruct N; symmetry in HeqN.
    apply IHs1 with (s2:=String ch s2) in HeqN.
    destruct or HeqN.
    2: right; rewrite <- append_assoc; apply HeqN.
    all: right; rewrite <- append_assoc; rewrite <- append_comm_cons.
    2: rewrite string_prenest_check'_append_nonzero in * by (rewrite HeqN; omega).
    all: rewrite HeqN in *; clear HeqN.
    all: cbn in *.
    - destruct ch as [b0 b1 b2 b3 b4 b5 b6 b7].
      all: destruct b0, b1, b2, b3.
      all: try solve [destruct n; [ | discriminate ]; auto].
      all: destruct b4, b5, b6, b7.
      all: try solve [destruct n; [ | discriminate ]; auto].
      discriminate.
      destruct n; [ auto | destruct n ]; [ auto | discriminate ].
    - destruct ch as [b0 b1 b2 b3 b4 b5 b6 b7].
      all: destruct b0, b1, b2, b3.
      all: try solve [discriminate].
      all: destruct b4, b5, b6, b7.
      all: try solve [discriminate].
      destruct N; [ auto | discriminate ].
  Qed.

  Lemma string_prenest_check'_append_inv_nonzero s1 s2 n:
    string_prenest_check' (s1 ++ s2) n > 0 ->
    s1 = ""%string \/ string_prenest_check' s1 n > 0.
  Proof.
    revert s2 n; induction s1; intros.
    now left.
    remember (string_prenest_check' (String a s1) n) as N.
    destruct N; symmetry in HeqN.
    apply string_prenest_check'_append_zero with (s2:=s2) in HeqN.
    destruct or HeqN; [ discriminate | omega ].
    right; omega.
  Qed.

  Lemma string_prenest_check'_add s n:
    string_prenest_check' s n > 0 ->
    forall m, string_prenest_check' s (n + m) =
              string_prenest_check' s n + m.
  Proof.
    revert n; induction s; intros.
    cbn; auto.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [ cbn in *; destruct n;
                     [ omega | rewrite plus_Sn_m;
                               rewrite <- plus_Sn_m;
                               now apply IHs ] ].
    all: destruct a4, a5, a6, a7.
    all: try solve [ cbn in *; destruct n;
                     [ omega | rewrite plus_Sn_m;
                               rewrite <- plus_Sn_m;
                               now apply IHs ] ].
    cbn in *; rewrite <- plus_Sn_m. now apply IHs.
    cbn in *; destruct n; [ omega | destruct n ]; [ omega | ].
    repeat rewrite plus_Sn_m; rewrite <- plus_Sn_m.
    now apply IHs.
  Qed.

  Lemma string_prenest_check'_lbrack s:
    string_prenest_check' s 0 > 0 ->
    get 0 s = Some "["%char.
  Proof.
    induction s; intros; cbn in *.
    omega.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3; try omega.
    all: destruct a4, a5, a6, a7; try omega.
    auto.
  Qed.


  (* Facts relating [string_prenest_check] and [string_nest_check] *)
  Lemma string_prenest_nest_eq_S:
    forall s n, string_prenest_check' s n > 0 ->
                string_nest_check' s (S n) = S (string_prenest_check' s n).
  Proof.
    induction s; intros.
    now cbn.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [cbn in *; destruct n; [ omega | auto ]].
    all: destruct a4, a5, a6, a7.
    all: try solve [cbn in *; destruct n; [ omega | auto ]].
    cbn in *; now apply IHs in H.
    cbn in *; destruct n; [ omega | destruct n ]; [ omega | ].
    now apply IHs in H.
  Qed.

  Lemma string_prenest_nest_eq_1:
    forall s n, n > 0 ->
                string_prenest_check' s n = 1 ->
                string_nest_check' s n = 1.
  Proof.
    induction s; intros n NZ P.
    now cbn in *.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [cbn in *; destruct n; [ omega | auto ]].
    all: destruct a4, a5, a6, a7.
    all: try solve [cbn in *; destruct n; [ omega | auto ]].
    cbn in *; destruct n; [ | destruct n ]; try omega.
    apply IHs; omega.
  Qed.

  Lemma string_prenest_check'_add_rbrack s:
    string_prenest_check' s 0 = 1 ->
    string_nest_check (s ++ "]")%string.
  Proof.
    intros; unfold string_nest_check; cbn in *.
    assert (string_nest_check' s 1 = 2). {
      replace 2 with (S (string_prenest_check' s 0)) by omega.
      apply string_prenest_nest_eq_S; omega.
    }
    rewrite string_nest_check'_append_nonzero by omega.
    rewrite H0; cbn; omega.
  Qed.

  Lemma string_prenest_check'_nest_check s:
    string_prenest_check' s 1 = 1 ->
    string_nest_check s.
  Proof.
    intros; apply string_prenest_nest_eq_1; omega.
  Qed.

  Lemma string_prenest_check'_substring s:
    string_prenest_check' s 0 = 1 ->
    string_nest_check (substring 1 (length s - 1) s).
  Proof.
    intros; destruct s.
    cbn in H; congruence.
    assert (Some a = Some "["%char). {
      replace (Some a) with (get 0 (String a s)) by (cbn; auto).
      apply string_prenest_check'_lbrack.
      rewrite H; omega.
    }
    inversion H0; subst; clear H0.
    cbn in *.
    replace (length s - 0) with (length s) by omega.
    rewrite substring_refl.
    now apply string_prenest_check'_nest_check.
  Qed.



  (* This is the spec for [split_nest] when applied to correctly
     nested strings. *)
  Fixpoint split_nest_check ls :=
    match ls with
    | [] => True
    | ""%string :: ls => False (* Empty strings not allowed *)
    | s :: ls =>
      string_nest_check s       (* All components are properly nested *)
      /\ (* Bracketed components contain just one loop *)
         (get 0 s = Some "["%char ->
          string_nest_check (substring 1 (length s - 2) s))
      /\ split_nest_check ls
    end.

  (* If the input string is correctly nested,
     then the output of [split_nest] is correct. *)
  Inductive split_nest_word : string -> Prop :=
  | snw_ch : forall ch, split_nest_word (String ch "")
  | snw_bracket : forall s, split_nest_word (String "[" s).
  Hint Constructors split_nest_word.

  Lemma split_nest'_simple_words:
    forall s n x wx w,
      In w (split_nest' s n x) ->
      (x = ""%string /\ n = 0 \/ x = String "[" wx) ->
      split_nest_word w.
  Proof.
    intros s n x; functional induction (split_nest' s n x); intros wx w I X.
    - destruct X as [[X N] | X].
      + apply (IHl ""%string w); auto.
        right; now subst.
      + apply (IHl (wx ++ "[")%string w); auto.
        right; now subst.
    - destruct X as [[X N] | X].
      + apply (IHl ""%string w); auto.
        right; now subst.
      + apply (IHl (wx ++ "[")%string w); auto.
        right; now subst.
    - destruct I.
      + destruct X as [[X N] | X]; subst; constructor.
      + destruct X as [[X N] | X]; apply (IHl wx w); auto.
    - destruct X as [[X N] | X].
      + discriminate.
      + apply (IHl (wx ++ "]")%string w); auto.
        right; now subst.
    - destruct I.
      + destruct X as [[X N] | X]; subst; constructor.
      + destruct X as [[X N] | X]; apply (IHl wx w); auto.
    - destruct X as [[X N] | X].
      + discriminate.
      + apply (IHl (wx ++ String ch "") w)%string; auto.
        right; now subst.
    - destruct I.
    - destruct X as [[X N] | X].
      + contradiction.
      + destruct I as [I | []]; subst; constructor.
  Qed.
      
  Inductive split_nest_xword : string -> Prop :=
  | snxw_ch : forall ch, string_nest_check (String ch "") -> split_nest_xword (String ch "")
  | snxw_nest : forall s, string_nest_check (String "[" s) ->
                          string_nest_check (substring 0 (length s - 1) s) ->
                          split_nest_xword (String "[" s).

  Lemma split_nest'_nested_words:
    forall s n x,
      (x = ""%string \/ n > 0) ->
      string_prenest_check' x 0 = n ->
      string_nest_check (x ++ s) ->
      forall w,
        In w (split_nest' s n x) ->
        split_nest_xword w.
  Proof.
    intros s n x P; functional induction (split_nest' s n x); intros;
      unfold string_prenest_check in *.
    - apply IHl; auto.
      + destruct or P; [ | omega ]; subst; now cbn.
      + rewrite <- append_assoc; now apply H0.
    - apply IHl; auto.
      + right; omega.
      + destruct or P; [ rewrite P in H; cbn in H; omega | ].
        rewrite string_prenest_check'_append_nonzero; auto.
        rewrite H; auto.
      + rewrite <- append_assoc; now apply H0.
    - assert (string_nest_check (x ++ "]")%string) as F. {
        now apply string_prenest_check'_add_rbrack.
      }
      assert (string_nest_check s0) as T. {
        apply string_nest_check_tail with (s1:=(x ++ "]")%string); auto.
        rewrite <- append_assoc; now cbn.
      }

      remember (x ++ "]")%string as X; destruct X.
      destruct x; cbn in *; discriminate.
      destruct H1; subst.
      rewrite HeqX in *.
      apply snxw_nest.
      + subst
      split; [ | split ]; auto.
      intros G; cbn.
      replace (substring 0 (length X - 1) X) with (substring 1 (length x - 1) x).
      now apply string_prenest_check'_substring.
      destruct x; cbn in *.
      inversion G; subst; discriminate.
      inversion HeqX.
      rewrite append_length; cbn.
      replace (length x + 1 - 1) with (length x) by omega.
      rewrite substring_append.
      replace (length x - 0) with (length x) by omega.
      apply substring_refl.
    - destruct n0; [ omega | ].
      apply IHl.
      + right; omega.
      + rewrite string_prenest_check'_append_nonzero; cbn;
          try rewrite H; auto; omega.
      + now rewrite <- append_assoc.
    - destruct or P; [ | omega ]; subst.
      cbn in *.
      split; [ | split ].
      + destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
        destruct a0, a1, a2, a3.
        all: try solve [now cbn].
        all: destruct a4, a5, a6, a7.
        all: try solve [now cbn].
      + intros; now cbn.
      + apply IHl; [ now left | auto | ].
        unfold string_nest_check in H0; cbn in H0.
        destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
        destruct a0, a1, a2, a3.
        all: try solve [apply H0].
        all: destruct a4, a5, a6, a7.
        all: try solve [apply H0].
        contradiction.
        discriminate.
    - apply IHl.
      + right; omega.
      + rewrite string_prenest_check'_append_nonzero; rewrite H; [ | omega ].
        destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
        destruct a0, a1, a2, a3.
        all: try solve [now cbn].
        all: destruct a4, a5, a6, a7.
        all: try solve [now cbn].
        destruct _x; contradiction.
      + now rewrite <- append_assoc.
    - now cbn.
    - destruct x; [ contradiction | ].
      destruct or P; [ discriminate | ].
      rewrite <- H in P.
      generalize (string_prenest_nest_eq_S (String a x) 0 P); intros G.
      destruct _x; [ omega | ].
      rewrite H in G.
      rewrite append_nil_r in H0; unfold string_nest_check in H0.
      rewrite H0 in G; omega.
  Qed.

  Lemma split_nest_correct:
    forall s, string_nest_check s ->
              split_nest_check (split_nest s).
  Proof.
    intros; apply split_nest'_correct.
    - now left.
    - now cbn.
    - now cbn.
  Qed.

  (* NB should also show that non-bracketed groups are a single character long *)

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

  Function parse_split_bf (l:list string) {measure sconcat_length l} : BF :=
    match l with
    | [] => bfz
    | ">" :: l => bfc bf_right (parse_split_bf l)
    | "<" :: l => bfc bf_left (parse_split_bf l)
    | "+" :: l => bfc bf_inc (parse_split_bf l)
    | "-" :: l => bfc bf_dec (parse_split_bf l)
    | "." :: l => bfc bf_out (parse_split_bf l)
    | "," :: l => bfc bf_in (parse_split_bf l)
    | (String "[" _) as s :: l =>
      let bn := parse_split_bf (split_nest (substring 1 (length s - 2) s)) in
      bfc (bf_loop bn) (parse_split_bf l)
    | "" :: l => bfz
    | _ :: l => parse_split_bf l
    end%string.
  Proof.
    all: intros; try solve [cbn; omega].
  
  Fixpoint parse_bns_bf (s:bneststring) : BF :=
    match s with
    | bns_empty => bfz
    | bns_ch ">" => bfc bf_right bfz
    | bns_ch "<" => bfc bf_left bfz
    | bns_ch "+" => bfc bf_inc bfz
    | bns_ch "-" => bfc bf_dec bfz
    | bns_ch "." => bfc bf_out bfz
    | bns_ch "," => bfc bf_in bfz
    | bns_ch _ => bfz
    | bns_app s1 s2 => bfapp (parse_bns_bf s1) (parse_bns_bf s2)
    | bns_nest s => bfc (bf_loop (parse_bns_bf s)) bfz
    end.

  Definition parse_bf (s:string) : option BF :=
    match parse_bns s bns_empty [] with
    | Some s => Some (parse_bns_bf s)
    | None => None
    end.

  Lemma bfapp_unparse:
    forall b1 b2, unparse_bns (bns_unparse_bf (bfapp b1 b2)) =
                  (unparse_bns (bns_unparse_bf b1) ++ unparse_bns (bns_unparse_bf b2))%string.
    induction b1; intros.
    - now cbn.
    - simpl; rewrite IHb1; now rewrite append_assoc.
  Qed.
 
  Lemma parse_bns_bf_correct (s:bneststring):
    unparse_bns (bns_unparse_bf (parse_bns_bf s)) = min_unparse_bns s.
  Proof.
    induction s.
    - cbn; auto.
    - cbn; destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
      destruct a0, a1, a2, a3.
      all: try solve [now cbn].
      all: destruct a4, a5, a6, a7.
      all: try solve [now cbn].
    - cbn; rewrite bfapp_unparse; rewrite IHs1; now rewrite IHs2.
    - simpl; rewrite IHs; now rewrite append_nil_r.
  Qed.

    
  Example parse_all_bf_commands:
    parse_bf "[><+-.,]" =
    Some (bfc (bf_loop
                 (bfc bf_right (bfc bf_left (bfc bf_inc (bfc bf_dec (bfc bf_out (bfc bf_in bfz))))))) bfz).
  now cbn. Qed.

  Example parse_nesting_bf:
    parse_bf "[[[][]]][]" =
    Some (bfc
            (bf_loop (bfc
                        (bf_loop (bfc
                                    (bf_loop bfz)
                                    (bfc (bf_loop bfz) bfz))) bfz))
            (bfc (bf_loop bfz) bfz)).
  now cbn. Qed.

  Example parse_empty_bf:
    parse_bf EmptyString = Some bfz.
  now cbn. Qed.

  Example parse_bf_bad_left:
    parse_bf "[[]" = None.
  auto. Qed.

  Example parse_bf_bad_right:
    parse_bf "[]]" = None.
  auto. Qed.

End BFParsing.



(* GARBAGE STARTS HERE *)

Fixpoint min_unparse_bns b :=
  match b with
  | bns_empty => ""%string
  | bns_ch ch => if is_bfchar_nb ch then String ch "" else ""%string
  | bns_app s1 s2 => (min_unparse_bns s1 ++ min_unparse_bns s2)%string
  | bns_nest s => String "[" (min_unparse_bns s ++ "]")
  end.

  Lemma unparse_equal:
    forall b, unparse_bf b = unparse_bns (bns_unparse_bf b).
  Proof.
    induction b using bf_mut
    with (P:=fun b => unparse_bf b = unparse_bns (bns_unparse_bf b))
           (P0:=fun b => unparse_bf (bfc b bfz) = unparse_bns (bns_unparse_bf1 b)).
    all: try solve [cbn; auto].
    cbn in IHb; rewrite append_nil_r in IHb.
    cbn; rewrite IHb; now rewrite IHb0.
    replace (unparse_bns (bns_unparse_bf1 (bf_loop b))) with (("[" ++ unparse_bf b ++ "]")%string).
    cbn; now rewrite append_nil_r.
    simpl; now rewrite <- IHb.
  Qed.


Inductive bneststring :=
| bns_empty
| bns_ch : ascii -> bneststring
| bns_app : bneststring -> bneststring -> bneststring
| bns_nest : bneststring -> bneststring.



Definition checked_cons {A} (s:A) ls :=
  match ls with
  | Some ls => Some (s :: ls)
  | None => None
  end.

Function checked_split_nest' s n x :=
  match s, n with
  | String "[" s, 0 => checked_split_nest' s 1 (x ++ "[")%string
  | String "[" s, S _ => checked_split_nest' s (S n) (x ++ "[")%string
  | String "]" s, 0 => None
  | String "]" s, 1 => checked_cons (x ++ "]")%string (checked_split_nest' s 0 ""%string)
  | String "]" s, S n => checked_split_nest' s n (x ++ "]")%string
  | String ch s, 0 => checked_cons (x ++ String ch "")%string (checked_split_nest' s n ""%string)
  | String ch s, S _ => checked_split_nest' s n (x ++ String ch "")%string
  | ""%string, 0 => Some []
  | ""%string, S _ => None
  end.

Definition checked_split_nest s := checked_split_nest' s 0 ""%string.

Lemma checked_split_nest_ok:
  forall s l, checked_split_nest s = Some l -> split_nest s = l.
Admitted.


Function parse_bns' (ls:list string) {measure sconcat_length ls} : bneststring :=
  match ls with
  | [] => bns_empty
  | ""%string :: ls => bns_empty
  | String ch "" :: ls => bns_app (bns_ch ch) (parse_bns' ls)
  | x :: ls => let l := length x in
               bns_app (parse_bns' (split_nest (substring 1 (l - 2) x))) (parse_bns' ls)
  end.
Proof.
  1-2: intros; cbn; try omega.
  intros; rewrite sconcat_length_eq.
  rewrite split_nest_sconcat.
  rewrite substring_length.
  cbn.
  rewrite Nat.min_lt_iff.
  omega.
Defined.

Definition parse_bns s := parse_bns' (split_nest s).

Inductive string_prenest_checker : string -> nat -> Prop :=
| spnc_start : string_prenest_checker "["%string 1
| spnc_lbrack : forall s n,
    string_prenest_checker s n ->
    string_prenest_checker (s ++ String "[" "")%string (S n)
| spnc_rbrack : forall s n,
    string_prenest_checker s (S (S n)) ->
    string_prenest_checker (s ++ String "]" "")%string (S n)
| spnc_ch : forall s ch n,
    string_prenest_checker s n ->
    ch <> "["%char ->
    ch <> "]"%char ->
    string_prenest_checker (s ++ String ch "")%string n.

Lemma string_prenest_checker_n:
  forall s n, string_prenest_checker s n -> n > 0.
Proof.
  intros; induction H; omega.
Qed.

Lemma string_prenest_check_match s n:
  string_prenest_checker s n <->
  (get 0 s = Some "["%char /\ string_prenest_check' s 0 = n /\ n > 0).
Proof.
  split.
  - intros SP.
    induction SP; cbn; auto; destruct_conjs.
    all: split; [ now apply append_get | split ]; [ | omega ].
    all: generalize (string_prenest_checker_n _ _ SP); intros G.
    all: rewrite string_prenest_check'_append_nonzero by omega.
    1, 2: rewrite H0; now cbn.
    rewrite H2; cbn.
    destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [now destruct n].
    all: destruct a4, a5, a6, a7.
    all: try solve [now destruct n].
  - revert n; induction s using reverse_ind; intros n G; destruct G as [G [S N]].
    cbn in G; discriminate.
    destruct s; simpl in G; inversion G; subst; clear G.
    cbn; constructor.

    assert (string_prenest_check' (String "[" s) 0 > 0) as G. {
      apply string_prenest_check'_append_inv_nonzero in N.
      destruct or N; [ discriminate | auto ].
    }
    assert (string_prenest_checker (String "[" s) (string_prenest_check' (String "[" s) 0)) as I. {
      apply IHs; split; [ | split]; cbn; auto.
    }
    clear IHs.
    apply string_prenest_check'_append_nonzero with (s2:=String ch "") in G.
    rewrite G in *.
    remember (string_prenest_check' (String "[" s) 0) as X; clear G HeqX.
    remember (string_prenest_check' (String ch "") X) as Y; symmetry in HeqY.
    destruct ch as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [apply spnc_ch; cbn in HeqY; destruct X; now subst].
    all: destruct a4, a5, a6, a7.
    all: try solve [apply spnc_ch; cbn in HeqY; destruct X; now subst].
    cbn in HeqY; subst; now constructor.
    cbn in HeqY; subst.
    destruct X; [ omega | destruct X; [ omega | subst ]].
    now constructor.
Qed.
    

(*
Function parse_bns s bns l :=
  match s with
  | String "[" s => parse_bns s bns_empty (bns :: l)
  | String "]" s => match l with
                    | bx :: l => parse_bns s (bns_app bx (bns_nest bns)) l
                    | [] => None
                    end
  | String ch s => parse_bns s (bns_app bns (bns_ch ch)) l
  | ""%string => match l with
                 | bx :: l => None
                 | [] => Some bns
                 end
  end.
 *)

Fixpoint unparse_bns b :=
  match b with
  | bns_empty => ""%string
  | bns_ch ch => String ch ""
  | bns_app s1 s2 => (unparse_bns s1 ++ unparse_bns s2)%string
  | bns_nest s => String "[" (unparse_bns s ++ "]")
  end.



Lemma parse_bns_correct':
  forall ls, split_nest_check' ls -> unparse_bns (parse_bns' ls) = sconcat ls.
Proof.
  intros ls; functional induction (parse_bns' ls); intros.
  - now cbn.
  - now cbn in H.
  - simpl; rewrite IHb; auto.
    now apply split_nest_check'_tail in H.
  - simpl in H.


    destruct x; try contradiction.
    destruct x; try contradiction.
    simpl in H.
    destruct a as [x0 a1 a2 a3 a4 a5 a6 a7].
    destruct x0, a1, a2, a3.
    all: try solve [contradict H].
    all: destruct a4, a5, a6, a7.
    all: try solve [contradict H].
    destruct_conjs.
    apply IHb0 in H0.
    simpl.
    induction s; cbn; auto.
  destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
  destruct a0, a1, a2, a3.


Definition split_nest_check ls :=
  ls = [""%string] \/ split_nest_check' ls.



Check bf_mut.

Lemma unparse_bf_cons bf1 bf:
  unparse_bf (bfc bf1 bf) = (unparse_bf1 bf1 ++ unparse_bf bf)%string.
  induction bf; cbn; reflexivity.
Qed.

Lemma unparse_bf1_eq bf1:
  unparse_bf (bfc bf1 bfz) = unparse_bf1 bf1.
  simpl; rewrite append_nil_r; auto.
Qed.

Lemma bf_parse_inv:
  forall bf, parse_bf (unparse_bf bf) = Some bf.
  induction bf using bf_mut
  with (P:=fun b => parse_bf (unparse_bf b) = Some b)
         (P0:=fun b => parse_bf (unparse_bf (bfc b bfz)) = Some (bfc b bfz)).
  1, 3-8: cbn; auto.

  rewrite unparse_bf_cons.
  unfold parse_bf in *.
  rewrite parse_bf'_app with (bp':=bfp (bfc b bfz) [] true).
  replace (unparse_bf bf) with ((unparse_bf bf ++ "")%string).
  rewrite parse_bf'_app with (bp':=bfp (bfapp (bfc b bfz) bf) [] true); auto.
  cbn.
  rewrite bfapp_bfz; now cbn.
  now rewrite append_nil_r.

  unfold unparse_bf; fold unparse_bf.
  unfold parse_bf; cbn.
  rewrite parse_bf'_app2 with (bs:=bf); auto.
  cbn.
  now rewrite bfapp_bfz.
Qed.


Lemma bf_print_parse_loop (bf1 bf2: BF):
  forall bf1' bf2',
    parse_bf_state (chars_of_bf bf1) = parse_ok bf1' [] ->
    parse_bf_state (chars_of_bf bf2) = parse_ok bf2' [] ->
    parse_bf_state ("["%char :: (chars_of_bf bf1) ++ ["]"%char]
                                  ++ (chars_of_bf bf2))
    = parse_ok (bf_loop bf1 bf2) [].
Proof.
  intros.
  cbn.
Admitted.

Lemma bf_print_parse_chars_inv (bf: BF):
  parse_bf_state (chars_of_bf bf) = parse_ok bf [].
Proof.
  induction bf; auto;
    rewrite chars_of_bf_equation, parse_bf_state_equation;
    try (rewrite IHbf; auto).
  now apply (bf_print_parse_loop _ _ bf1 bf2).
Qed.

Lemma chars_of_string_of_chars_inv (l: list ascii):
  chars_of_string (string_of_chars l) = l.
Proof.
  induction l; auto.
  rewrite string_of_chars_equation, chars_of_string_equation.
  now rewrite IHl.
Qed.

(* Removes the parser from the trusted computing base *)
Theorem bf_print_parse_inv (bf: BF): parse_bf (print_bf bf) = Some bf.
Proof.
  unfold parse_bf, print_bf; rewrite chars_of_string_of_chars_inv.
  now rewrite bf_print_parse_chars_inv.
Qed.

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
