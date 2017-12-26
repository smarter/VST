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

Infix "<<" := Z.shiftl (at level 51, left associativity).
Infix ">>" := Z.shiftr (at level 51, left associativity).

Definition od_add_spec : ident * funspec :=
 DECLARE _od_add
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >> 1 <= p0 <= Int.max_signed >> 1;
                 Int.min_signed >> 1 <= p1 <= Int.max_signed >> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (p0 + p1))))
          SEP ().

Definition od_sub_spec : ident * funspec :=
 DECLARE _od_sub
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >> 1 <= p0 <= Int.max_signed >> 1;
                 Int.min_signed >> 1 <= p1 <= Int.max_signed >> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (p0 - p1))))
          SEP ().

Definition od_add_avg_spec : ident * funspec :=
 DECLARE _od_add_avg
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >> 1 <= p0 <= Int.max_signed >> 1;
                 Int.min_signed >> 1 <= p1 <= Int.max_signed >> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr ((p0 + p1) >> 1))))
          SEP ().

Definition od_mul_Z := fun (n c q: Z) => ((n*c + ((1 << q) >> 1)) >> q).

Definition od_mul_spec : ident * funspec :=
 DECLARE _od_mul
  WITH n: Z, c: Z, q: Z
  PRE [ _n OF tint, _c OF tint, _q OF tint ]
          PROP  (Int.min_signed >> 17 <= n <= Int.max_signed >> 17; 0 <= c <= 65535; 0 <= q <= 15)
          LOCAL (temp _n (Vint (Int.repr n)); temp _c (Vint (Int.repr c)); temp _q (Vint (Int.repr q)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (od_mul_Z n c q))))
          SEP ().

Definition od_rot2_spec : ident * funspec :=
 DECLARE _od_rot2
  WITH p0: val, p1: val, sh: share, t: Z, c0: Z, q0: Z, c1: Z, q1: Z, i0: Z
  PRE [ _p0 OF (tptr tint), _p1 OF (tptr tint), _t OF tint, _c0 OF tint, _q0 OF tint, _c1 OF tint, _q1 OF tint ]
          PROP  (readable_share sh;
                 Int.min_signed >> 17 <= i0 <= Int.max_signed >> 17; 0 <= c0 <= 65535; 0 <= q0 <= 15;
                 0 <= c1 <= 65535; 0 <= q1 <= 15)
          LOCAL (temp _p0 p0; temp _p1 p1;
                 temp _c0 (Vint (Int.repr c0)); temp _q0 (Vint (Int.repr q0));
                 temp _c1 (Vint (Int.repr c1)); temp _q1 (Vint (Int.repr q1)))
          SEP   (data_at sh (tptr tint) (Vint (Int.repr i0)) p0)
  POST [ tvoid ] EX o0: Z, EX o1: Z,
          PROP (o0 = (od_mul_Z i0 c0 q0);
                o1 = (od_mul_Z o0 c0 q0))
          LOCAL ()
          SEP (data_at sh (tptr tint) (Vint (Int.repr o0)) p0;
               data_at sh (tptr tint) (Vint (Int.repr o1)) p1).

Definition od_fdct_2_spec : ident * funspec :=
 DECLARE _od_fdct_2
  WITH p0: val, p1: val, sh : share, i0: Z, i1: Z(* , o0: Z, o1: Z *)
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
  ltac:(with_library prog [
    sumtwo_spec; od_add_spec; od_add_avg_spec; od_mul_spec; od_rot2_spec; od_fdct_2_spec
  ]).

Lemma add_le_2: forall min max a b: Z, Zeven min ->
                                       min < 0                   -> max > 0 ->
                                       min >> 1 <= a <= max >> 1 -> min >> 1 <= b <= max >> 1 ->
                                       min <= a + b <= max.
  intros.
  split.

  replace min with ((min >> 1) + (min >> 1)).
  apply Z.add_le_mono; omega.
  symmetry.
  rewrite Z.add_diag.
  unfold Z.shiftr.
  simpl.
  apply Zeven_div2.
  trivial.

  destruct Zeven_odd_dec with max.
  - replace max with ((max >> 1) + (max >> 1)).
    apply Z.add_le_mono; omega.
    rewrite Z.add_diag.
    unfold Z.shiftr.
    simpl.
    symmetry.
    apply Zeven_div2.
    trivial.
  - replace max with ((max >> 1) + (max >> 1) + 1).
    apply Z.le_trans with ((max >> 1) + (max >> 1)).
    apply Z.add_le_mono; omega.
    omega.
    rewrite Z.add_diag.
    unfold Z.shiftr.
    simpl.
    symmetry.
    apply Zodd_div2.
    trivial.
Qed.

Lemma body_od_add: semax_body Vprog Gprog f_od_add od_add_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_od_sub: semax_body Vprog Gprog f_od_sub od_sub_spec.
Proof.
  start_function.
  forward.
Qed.

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
  apply add_le_2; try (easy || repable_signed).
Qed.

Lemma conj_same: forall P: Prop, P -> P /\ P.
  intros.
  split; trivial.
Qed.

Lemma shiftl_le: forall m p q, m > 0 -> p >= 0 -> q >= 0 -> p <= q -> (m << p) <= (m << q).
  intros.
  repeat rewrite Int.Zshiftl_mul_two_p; try omega.
  apply Z.mul_le_mono_pos_l.
  omega.
  apply two_p_monotone.
  omega.
Qed.

Lemma shr_signed: forall m n,
    Int.min_signed <= m <= Int.max_signed ->
    0 <= n <= Int.max_unsigned ->
    Int.repr (m >> n) = Int.shr (Int.repr m) (Int.repr n).
  intros.
  unfold Int.shr.
  f_equal.
  rewrite Int.signed_repr, Int.unsigned_repr; auto.
Qed.

Lemma body_od_mul: semax_body Vprog Gprog f_od_mul od_mul_spec.
Proof.
  start_function.

  assert(ltu_q_wordsize: Int.ltu (Int.repr q) Int.iwordsize = true).
    unfold Int.ltu.
    rewrite zlt_true.
    simpl.
    trivial.

    unfold Int.iwordsize.
    unfold Int.zwordsize.
    simpl.
    repeat rewrite Int.unsigned_repr.
    omega.
    repable_signed.
    repable_signed.

  assert (pow2_q_signed: Int.min_signed <= 1 << q <= Int.max_signed).
    split.
    (**) apply Z.le_trans with (1 << 0).
      simpl.
      repable_signed.
      apply shiftl_le; omega.
    (**) apply Z.le_trans with (1 << 15).
      apply shiftl_le; omega.
      unfold Int.max_signed; simpl; omega.


  forward.
  entailer!.
  apply conj_same.
  rewrite ltu_q_wordsize.
  unfold is_true. trivial.

  entailer!.
  unfold sem_shift, sem_shift_ii.
  simpl.
  rewrite ltu_q_wordsize.
  simpl.
  f_equal.

  (* Lemma add_signed: forall m n, *)
  (*     (* Int.min_signed <= m <= Int.max_signed -> *) *)
  (*     (* 0 <= n <= Int.max_unsigned -> *) *)
  (*     Int.repr (m + n) = Int.shr (Int.repr m) (Int.repr n). *)

  unfold od_mul_Z.
  rewrite shr_signed.
  f_equal.
  rewrite Int.add_signed.
  f_equal.
  repeat rewrite Int.signed_repr.
  f_equal.

  unfold Int.shr, Int.shl.
  repeat rewrite Int.signed_repr, Int.unsigned_repr; try repable_signed.
  rewrite Int.unsigned_repr.
  normalize. repable_signed.
  normalize.
  
  (* Int.min_signed <= 1 << q >> 1 <= Int.max_signed *)
  split.
  (**)  apply Z.le_trans with ((1 << 0) >> 1).
    unfold Int.min_signed, Z.shiftr; simpl; omega.
    repeat rewrite Z.shiftr_div_pow2.
    simpl.
    unfold Z.pow_pos. simpl.
    apply Z.div_le_mono.
    omega.
    apply Z.le_trans with (1 << 0).
    simpl. omega.
    apply shiftl_le; omega.
    omega.
    omega.
  (**) apply Z.le_trans with ((1 << 15) >> 1).
    repeat rewrite Z.shiftr_div_pow2.
    apply Z.div_le_mono.
    simpl.
    unfold Z.pow_pos. simpl.
    omega.
    apply shiftl_le; omega.
    omega.
    omega.
    unfold Int.max_signed, Z.shiftr; simpl; omega.
    normalize.

  split.
  (**) admit.
  (**) admit.
  split.
  (**) admit.
  (**) admit.

  split; repable_signed.
Admitted.

Lemma body_od_rot2: semax_body Vprog Gprog f_od_rot2 od_rot2_spec.
Proof.
  start_function.
  forward_call (i0, c0, q0).
  forward.
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
