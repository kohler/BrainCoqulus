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

Lemma append_nil_r:
  forall s, (s ++ "" = s)%string.
  induction s; cbn; try rewrite IHs; auto.
Qed.

Lemma append_assoc:
  forall s1 s2 s3, (s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3)%string.
  induction s1; cbn; intros; auto.
  now rewrite IHs1.
Qed.

Lemma append_length:
  forall s1 s2, (length (s1 ++ s2) = length s1 + length s2)%string.
  induction s1; cbn; auto.
Qed.

Lemma append_inv_ch_tail:
  forall s1 s2 ch, (s1 ++ String ch "" = s2 ++ String ch "" -> s1 = s2)%string.
  induction s1; intros.
  destruct s2; simpl in H; auto.
  generalize (append_length (String a "") (s2 ++ String ch "")); intro L.
  replace ((String a "" ++ s2 ++ String ch "")%string) with ((String a (s2 ++ String ch ""))%string) in L by (now cbn).
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
  forall s1 s2 s, (s1 ++ s = s2 ++ s -> s1 = s2)%string.
Proof.
  intros s1 s2 s; revert s1 s2; induction s; intros.
  now repeat rewrite append_nil_r in H.
  replace (String a s) with ((String a EmptyString ++ s)%string) in H by (now cbn).
  repeat rewrite append_assoc in H.
  apply IHs in H.
  now apply append_inv_ch_tail in H.
Qed.

Lemma append_tail:
  forall s1 s2 s, (s1 = s2 -> s1 ++ s = s2 ++ s)%string.
  intros; now subst.
Qed.

Lemma substring_empty:
  forall n s, substring n 0 s = ""%string.
  induction n; cbn.
  destruct s; auto.
  intros; destruct s; cbn; auto.
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


Inductive bneststring :=
| bns_empty
| bns_ch : ascii -> bneststring
| bns_app : bneststring -> bneststring -> bneststring
| bns_nest : bneststring -> bneststring.

Fixpoint unparse_bns b :=
  match b with
  | bns_empty => ""%string
  | bns_ch ch => String ch ""
  | bns_app s1 s2 => (unparse_bns s1 ++ unparse_bns s2)%string
  | bns_nest s => String "[" (unparse_bns s ++ "]")
  end.


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

  Fixpoint bns_unparse_bf1 (bf1:BF1) : bneststring :=
    match bf1 with
    | bf_right => bns_ch ">"
    | bf_left => bns_ch "<"
    | bf_inc => bns_ch "+"
    | bf_dec => bns_ch "-"
    | bf_out => bns_ch "."
    | bf_in => bns_ch ","
    | bf_loop inner => bns_nest (bns_unparse_bf inner)
    end
  with
    bns_unparse_bf (bf:BF) : bneststring :=
      match bf with
      | bfz => bns_empty
      | bfc a bf' => bns_app (bns_unparse_bf1 a) (bns_unparse_bf bf')
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


  Function make_bns s bns l :=
    match s with
    | String "[" s => make_bns s bns_empty (bns :: l)
    | String "]" s => match l with
                      | bx :: l => make_bns s (bns_app bx (bns_nest bns)) l
                      | [] => None
                      end
    | String ch s => make_bns s (bns_app (bns_ch ch) bns) l
    | ""%string => match l with
                   | bx :: l => None
                   | [] => Some bns
                   end
    end.

  Lemma make_bns_suffix s b l b':
    make_bns s b l = Some b' -> exists s', unparse_bns b' = (s' ++ s)%string.
    revert b l b'; induction s; cbn; intros.
    exists (unparse_bns b'); now rewrite append_nil_r.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    apply IHs in H.
    destruct H as [s' H].

  Lemma make_bns_correct s b:
    make_bns s bns_empty [] = Some b -> unparse_bns b = s.
    revert b; induction s; cbn; intros.
    inversion H; subst; now cbn.
    simpl; intros.
    forall bns,
    


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
    match make_bns s bns_empty [] with
    | Some s => Some (parse_bns_bf s)
    | None => None
    end.

  

  

  Definition otherch : ascii -> Prop :=
    fun a =>
      match a with
      | ">" | "<" | "+" | "-" | "." | "," | "[" | "]" => False
      | _ => True
      end%char.


  Function parse_bf' (s:string) (b:BF) (l:list BF)
  : option BF :=
    match s with
    | ""%string => match l with
                   | [] => Some b
                   | _ => None
                   end
    | String ">" s => parse_bf' s (bfrevc b bf_right) l
    | String "<" s => parse_bf' s (bfrevc b bf_left) l
    | String "+" s => parse_bf' s (bfrevc b bf_inc) l
    | String "-" s => parse_bf' s (bfrevc b bf_dec) l
    | String "." s => parse_bf' s (bfrevc b bf_out) l
    | String "," s => parse_bf' s (bfrevc b bf_in) l
    | String "[" s => parse_bf' s bfz (b :: l)
    | String "]" s => match l with
                      | [] => None
                      | bx :: l' =>
                        parse_bf' s (bfrevc bx (bf_loop b)) l'
                      end
    | String _ s => parse_bf' s b l
    end.

  Definition parse_bf (s:string) : option BF :=
    parse_bf' s bfz [].
  Hint Resolve parse_bf.


  Lemma parse_bf'_app:
    forall s1 b1 l1 b s2,
      parse_bf' s1 b1 l1 = Some b ->
      parse_bf' (s1 ++ s2) b1 l1 = parse_bf' s2 b [].
  Proof.
    induction s1; intros.
    destruct l1; cbn in *; inversion H; now subst.
    cbn in H.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [cbn; now apply IHs1].
    all: destruct a4, a5, a6, a7.
    all: try solve [cbn; now apply IHs1].
    destruct l1; try discriminate.
    cbn; now apply IHs1.
  Qed.

  Lemma parse_bf'_empty:
    forall s b b',
      parse_bf' s bfz [] = Some b ->
      parse_bf' s b' [] = Some (bfapp b' b).
    induction s; intros.
    cbn in *; inversion H; subst.
    now rewrite bfapp_bfz_r.

    cbn in H.
    destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
    destruct a0, a1, a2, a3.
    all: try solve [cbn; now apply IHs with (b:=b)].
    all: destruct a4, a5, a6, a7.
    all: try solve [cbn; now apply IHs with (b:=b)].
    Focus 2.
    apply IHs in H. destruct H as [bn [H H0]].
    exists (bfc bf_inc bn).
    cbn.
      parse_bf' s b [] = bfapp b (parse_bf' s bfz []).

  Lemma parse_bf_app:
    forall s1 s2 b1 b2,
      parse_bf s1 = Some b1 ->
      parse_bf s2 = Some b2 ->
      parse_bf (s1 ++ s2) = Some (bfapp b1 b2).
    induction s1; intros.
    cbn in *; inversion H; subst; now rewrite bfapp_bfz_l.

  Lemma parse_bf'_app:
    forall s1 bf bf' s2 l,
      parse_bf s1 = Some bf' ->
      parse_bf' (s1 ++ s2) bf l = parse_bf' s2 (bfapp bf bf') l.
    induction s1; intros.
    cbn in *; inversion H; subst; now rewrite bfapp_bfz_r.
    cbn in *. now apply IHs1.
  Qed.


  Lemma bnest_parseable:
    forall s, bneststring s -> exists b, parse_bf s = Some b.
  Proof.
    intros s BN; induction BN.
    - exists bfz; now cbn.
    - destruct ch as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3.
      all: try solve [exists bfz; now cbn].
      all: destruct b4, b5, b6, b7.
      all: try solve [exists bfz; now cbn].
      1: exists (bfc bf_inc bfz).
      2: exists (bfc bf_dec bfz).
      3: exists (bfc bf_right bfz).
      4: exists (bfc bf_out bfz).
      5: exists (bfc bf_left bfz).
      6: exists (bfc bf_in bfz).
      all: now cbn.
    -
      all: ( exists (bfc bf_inc bfz) | exists (bfc bf_dec bfz) |
                   exists (bfc bf_right bfz) | exists (bfc bf_out bfz) |
                   exists (bfc bf_left bfz) | exists (bfc bf_in bfz) ].
  Lemma parse_bf_bnest_app:
    forall s, bneststring s ->
              forall b, parse_bf s = Some b ->
                        forall s' b' l, parse_bf' (s ++ s') b' l = parse_bf' s' (bfapp b' b) l.
  Proof.
    intros s BN; induction BN; intros b P s' b' l; cbn in P.
    - inversion P; subst; now rewrite bfapp_bfz_r.
    - destruct ch as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3.
      all: try solve [inversion P; subst; now rewrite bfapp_bfz_r].
      all: destruct b4, b5, b6, b7.
      all: try solve [inversion P; subst; now rewrite bfapp_bfz_r].
      all: try solve [inversion P; subst; now rewrite bfapp_singleton_r].
    - 
      
  Lemma parse_bf_bnest:
    forall s, (exists b, parse_bf s = Some b) <-> bneststring s.
  Proof.
    split.
    - admit.
    - intro BN; induction BN.
      + exists bfz; now cbn.
      + destruct ch as [b0 b1 b2 b3 b4 b5 b6 b7].
        destruct b0, b1, b2, b3, b4, b5, b6, b7.
        all: try solve [exists bfz; cbn; reflexivity].
        1, 3: contradiction.
        exists (bfc bf_inc bfz); now cbn.
        exists (bfc bf_dec bfz); now cbn.
        exists (bfc bf_right bfz); now cbn.
        exists (bfc bf_out bfz); now cbn.
        exists (bfc bf_left bfz); now cbn.
        exists (bfc bf_in bfz); now cbn.
      + destruct IHBN
                  1: 

  Inductive BFParse :=
  | bfp : BF -> list BF -> bool -> BFParse.

  Notation bfpf := (BF -> option string -> option BF).


  Function skip_brackets' (s:string) (n:nat) : option nat :=
    match s, n with
    | String "]" s, 0 => Some (length s)
    | String "]" s, S n => skip_brackets' s n
    | String "[" s, n => skip_brackets' s (S n)
    | String _ s, n => skip_brackets' s n
    | ""%string, _ => None
    end.

  Definition skip_brackets s : option (string * string) :=
    match skip_brackets' s 0 with
    | Some l => Some (substring 0 (length s - l - 1) s,
                      substring (length s - l) l s)
    | None => None
    end.

  Lemma skip_brackets'_length:
    forall s n x, skip_brackets' s n = Some x -> x < length s.
    intros s n; functional induction (skip_brackets' s n).
    intros; inversion H; subst; cbn; omega.
    1-3: intros; apply IHo in H; cbn; omega.
    intros; discriminate.
  Qed.

  Lemma skip_brackets_length:
    forall s s1 s2, skip_brackets s = Some (s1, s2) ->
                    length s = length s1 + length s2 + 1.
    intros; unfold skip_brackets in H.
    remember (skip_brackets' s 0) as sb; destruct sb; try discriminate.
    inversion H; subst.
    symmetry in Heqsb; apply skip_brackets'_length in Heqsb.
    repeat rewrite substring_length.
    replace (length s - (length s - n)) with n by omega.
    replace (length s - 0) with (length s) by omega.
    rewrite Min.min_idempotent.
    replace (Nat.min (length s - n - 1) (length s)) with (length s - n - 1).
    omega.
    assert (length s - n - 1 <= length s) by omega.
    now rewrite Min.min_l.
  Qed.

  Example skip_brackets1:
    (skip_brackets "]" = Some ("", "")
     /\ skip_brackets "abc]def" = Some ("abc", "def")
     /\ skip_brackets "a[[][c]]d]e" = Some ("a[[][c]]d", "e")
    )%string.
  now cbn. Qed.


  (*
  Fixpoint parse_bf' (s:string) : BF :=
    match s with
    | String ">" s => bfc bf_right (parse_bf' s)
    | String "<" s => bfc bf_left (parse_bf' s)
    | String "+" s => bfc bf_inc (parse_bf' s)
    | String "-" s => bfc bf_dec (parse_bf' s)
    | String "." s => bfc bf_out (parse_bf' s)
    | String "," s => bfc bf_in (parse_bf' s)
    | String "[" s => match skip_brackets s with
                      | Some (s1, s2) =>
                        match parse_bf' s1 bfz with
                        | Some bfn =>
                          parse_bf' s2 (bfrevc b (bf_loop bfn))
                        | None => None
                        end
                      | None => None
                      end
    | String "]" _ => None
    | String _ s => parse_bf' s
    | ""%string => bfz
    end.
  all: intros; subst.
  all: try solve [cbn; omega].
  all: apply skip_brackets_length in teq9.
  all: cbn; rewrite teq9; omega.
  Qed.

  Fixpoint parse_bf' s bp :=
    match s with
    | "" => bp
    | String ch s => parse_bf' s (parse_bfch ch bp)
    end%string.

  Definition parse_bf s :=
    match parse_bf' s (bfp bfz [] true) with
    | bfp b [] true => Some b
    | _ => None
    end.
   *)

  Lemma parse_bf'_app:
    forall s1 bf bf' s2 l,
      parse_bf s1 = Some bf' ->
      parse_bf' (s1 ++ s2) bf l = parse_bf' s2 (bfapp bf bf') l.
    induction s1; intros.
    cbn in *; inversion H; subst; now rewrite bfapp_bfz_r.
    cbn in *. now apply IHs1.
  Qed.

  Lemma parse_bf_back:
    forall l b s1 bf,
      parse_bf s1 = Some bf ->
      parse_bf' s1 (bfp b l true) = bfp (bfapp b bf) l true.
    induction s1.
    admit.
    
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
