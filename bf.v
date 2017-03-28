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

Lemma append_nil_r:
  forall s, (s ++ "" = s)%string.
  induction s; cbn; try rewrite IHs; auto.
Qed.


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

  Definition otherch : ascii -> Prop :=
    fun a =>
      match a with
      | ">" | "<" | "+" | "-" | "." | "," | "[" | "]" => False
      | _ => True
      end%char.


  (*
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
*)

  Inductive BFParse :=
  | bfp : BF -> list BF -> bool -> BFParse.

  Definition parse_bfch (ch:ascii) (bp:BFParse) : BFParse :=
    match ch, bp with
    | ">", bfp b l ok => bfp (bfrevc b bf_right) l ok
    | "<", bfp b l ok => bfp (bfrevc b bf_left) l ok
    | "+", bfp b l ok => bfp (bfrevc b bf_inc) l ok
    | "-", bfp b l ok => bfp (bfrevc b bf_dec) l ok 
    | ".", bfp b l ok => bfp (bfrevc b bf_out) l ok
    | ",", bfp b l ok => bfp (bfrevc b bf_in) l ok
    | "[", bfp b l ok => bfp bfz (b :: l) ok
    | "]", bfp b (bx :: l) ok => bfp (bfrevc bx (bf_loop b)) l ok
    | "]", bfp b [] _ => bfp b [] false
    | _, _ => bp
    end%char.

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

  Lemma parse_bf'_app:
    forall s1 bp bp' s2,
      parse_bf' s1 bp = bp' ->
      parse_bf' (s1 ++ s2) bp = parse_bf' s2 bp'.
    induction s1; intros.
    cbn in *; subst; reflexivity.
    cbn in *. now apply IHs1.
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
