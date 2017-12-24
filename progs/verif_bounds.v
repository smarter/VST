Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.progs.bounds. (* Import the AST of this C program *)
Require Import BinInt.
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(* Functional spec of this program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; omega.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition sumtwo_spec : ident * funspec :=
 DECLARE _sumtwo
  WITH sh : share, a: Z, b: Z
  PRE [ _a OF tuchar, _b OF tuchar ]
          PROP  (readable_share sh; 0 <= a <= 255; 0 <= b <= 255)
          LOCAL (temp _a (Vint (Int.repr a)); temp _b (Vint (Int.repr b)))
          SEP   (TT)
  POST [ tshort ]
          PROP (0 <= (a + b) <= 510)
          LOCAL(temp ret_temp  (Vint (Int.repr (a + b))))
          SEP (TT).

Definition od_add_spec : ident * funspec :=
 DECLARE _od_add
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed/2 <= p0 <= (Int.max_signed - 1)/2; Int.min_signed/2 <= p1 <= (Int.max_signed - 1)/2)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP (Int.min_signed <= p0 + p1 <= Int.max_signed - 1)
          LOCAL (temp ret_temp (Vint (Int.repr (p0 + p1))))
          SEP ().

Definition od_sub_spec : ident * funspec :=
 DECLARE _od_sub
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed/2 <= p0 <= (Int.max_signed - 1)/2; Int.min_signed/2 <= p1 <= (Int.max_signed - 1)/2)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP (Int.min_signed <= p0 + p1 <= Int.max_signed - 1)
          LOCAL (temp ret_temp (Vint (Int.repr (p0 - p1))))
          SEP ().

Definition od_add_avg_spec : ident * funspec :=
 DECLARE _od_add_avg
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed/2 <= p0 <= (Int.max_signed - 1)/2; Int.min_signed/2 <= p1 <= (Int.max_signed - 1)/2)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr ((p0 + p1) / 2))))
          SEP ().

Definition od_fdct_2_spec : ident * funspec :=
 DECLARE _od_fdct_2
  WITH p0: val, p1: val, sh : share, i0: Z, i1: Z, o0: Z, o1: Z
  PRE [ _p0 OF (tptr tint), _p1 OF (tptr tint) ]
          PROP  (readable_share sh; 0 <= i0 <= 8191; 0 <= i1 <= 8191)
          LOCAL (temp _p0 p0; temp _p1 p1)
          SEP   (data_at sh (tptr tint) (Vint (Int.repr i0)) p0;
                 data_at sh (tptr tint) (Vint (Int.repr i1)) p1)
  POST [tvoid] EX o0: Z, EX o1: Z,
          PROP (-32768 <= o0 <= 32767; -32768 <= o1 <= 32767)
          LOCAL ()
          SEP (data_at sh (tptr tint) (Vint (Int.repr o0)) p0;
               data_at sh (tptr tint) (Vint (Int.repr o1)) p1).

Definition Gprog : funspecs :=
        ltac:(with_library prog [sumtwo_spec; od_add_spec; od_add_avg_spec; od_fdct_2_spec]).

Lemma add_le_2: forall min max a b: Z, min mod 2 = 0        -> max mod 2 = 0       ->
                                       min < 0              -> max > 0             ->
                                       min/2 <= a <= max/2  -> min/2 <= b <= max/2 ->
                                       min <= a + b <= max.
  intros.
  split.

  replace min with (min/2 + min/2).
  apply Z.add_le_mono; omega.
  symmetry.
  rewrite Z.add_diag.
  apply Z_div_exact_full_2; omega.

  replace max with (max/2 + max/2).
  apply Z.add_le_mono; omega.
  rewrite Z.add_diag.
  symmetry.
  apply Z_div_exact_full_2; omega.
Qed.

Lemma body_od_add: semax_body Vprog Gprog f_od_add od_add_spec.
Proof.
  start_function.
  forward.
  entailer!.
  unfold Int.min_signed in *.
  simpl in *.
  apply add_le_2; try (auto || omega).
Qed.

Lemma body_od_sub: semax_body Vprog Gprog f_od_sub od_sub_spec.
Proof.
  start_function.
  forward.
  entailer!.
  unfold Int.min_signed in *.
  simpl in *.
  apply add_le_2; try (auto || omega).
Qed.

Require Import Psatz.
Lemma body_od_add_avg: semax_body Vprog Gprog f_od_add_avg od_add_avg_spec.
Proof.
  start_function.
  forward_call (p0, p1).
  forward.
  entailer!.
  f_equal.
  unfold Int.shr.
  rewrite Int.signed_repr.
  rewrite Int.unsigned_repr.
  rewrite Z.shiftr_div_pow2.
  auto.
  omega.
  repable_signed.
  omega.
Qed.

Lemma body_od_fdct_2: semax_body Vprog Gprog f_od_fdct_2 od_fdct_2_spec.
Proof.
  start_function.

Qed.

Lemma body_sumarray: semax_body Vprog Gprog f_sumtwo sumtwo_spec.
Proof.
  start_function.
  forward.
  repeat split; try omega.
  f_equal.
  apply Int.same_bits_eq.
  intros.
  rewrite sign_ext_inrange.
  reflexivity.
  rewrite Int.signed_repr.
  simpl.
  omega.
  repable_signed.
Qed.


(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.
forward_call (*  s = sumarray(four,4); *)
  (four,Ews,four_contents,4).
 split3; auto.
   computable.
   repeat constructor; computable.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sumarray.
semax_func_cons body_main.
Qed.
