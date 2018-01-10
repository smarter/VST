Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.progs.bounds. (* Import the AST of this C program *)
Require Import BinInt.
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Infix "<<<" := Z.shiftl (at level 51, left associativity).
Infix ">>>" := Z.shiftr (at level 51, left associativity).

Definition od_add_Z := fun (p0 p1: Z) => p0 + p1.
Hint Unfold od_add_Z.

Definition od_add_spec : ident * funspec :=
 DECLARE _od_add
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >>> 1 <= p0 <= Int.max_signed >>> 1;
                 Int.min_signed >>> 1 <= p1 <= Int.max_signed >>> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (od_add_Z p0 p1))))
          SEP ().

Definition od_sub_Z := fun (p0 p1: Z) => p0 - p1.
Hint Unfold od_sub_Z.

Definition od_sub_spec : ident * funspec :=
 DECLARE _od_sub
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >>> 1 <= p0 <= Int.max_signed >>> 1;
                 Int.min_signed >>> 1 <= p1 <= Int.max_signed >>> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (od_sub_Z p0 p1))))
          SEP ().

Definition od_add_avg_Z := fun (p0 p1: Z) => (od_add_Z p0 p1) >>> 1.
Hint Unfold od_add_avg_Z.

Definition od_add_avg_spec : ident * funspec :=
 DECLARE _od_add_avg
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >>> 1 <= p0 <= Int.max_signed >>> 1;
                 Int.min_signed >>> 1 <= p1 <= Int.max_signed >>> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (od_add_avg_Z p0 p1))))
          SEP ().

Definition od_sub_avg_Z := fun (p0 p1: Z) => (od_sub_Z p0 p1) >>> 1.
Hint Unfold od_sub_avg_Z.

Lemma od_sub_avg_bounded : forall p0 p1 max: Z, max > 0 -> -max-1 <= p0 <= max -> -max-1 <= p1 <= max ->
                                                    -max-1 <= od_sub_avg_Z p0 p1 <= max.
  intros.
  split.
  unfold od_sub_avg_Z, Z.shiftr. simpl.
  rewrite Z.div2_div.
  apply Z.div_le_lower_bound.
  omega.
  unfold od_sub_Z.
  omega.
  unfold od_sub_avg_Z, od_sub_Z, Z.shiftr.
  simpl.
  apply Z.le_trans with (Z.div2 (1 + max*2)).
  repeat rewrite Z.div2_div.
  apply Z.div_le_mono; omega.
  rewrite Z.div2_div.
  rewrite Z_div_plus.
  unfold Z.div. simpl. omega. omega.
Qed.

Definition od_sub_avg_spec : ident * funspec :=
 DECLARE _od_sub_avg
  WITH p0: Z, p1: Z
  PRE [ _p0 OF tint, _p1 OF tint ]
          PROP  (Int.min_signed >>> 1 <= p0 <= Int.max_signed >>> 1;
                 Int.min_signed >>> 1 <= p1 <= Int.max_signed >>> 1)
          LOCAL (temp _p0 (Vint (Int.repr p0)); temp _p1 (Vint (Int.repr p1)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (od_sub_avg_Z p0 p1))))
          SEP ().

Definition od_shr_round_Z := fun (x shift: Z) => (x + ((1 <<< shift) >>> 1)) >>> shift.
Hint Unfold od_shr_round_Z.
Definition od_mul_Z := fun (n c q: Z) => od_shr_round_Z (n*c) q.
Hint Unfold od_mul_Z.

Definition od_mul_spec : ident * funspec :=
 DECLARE _od_mul
  WITH n: Z, c: Z, q: Z
  PRE [ _n OF tint, _c OF tint, _q OF tint ]
          PROP  (Int.min_signed >>> 17 <= n <= Int.max_signed >>> 17; 0 <= c <= 65535; 0 <= q <= 15;
                 1 <<< q < c)
          LOCAL (temp _n (Vint (Int.repr n)); temp _c (Vint (Int.repr c)); temp _q (Vint (Int.repr q)))
          SEP   ()
  POST [ tint ]
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr (od_mul_Z n c q))))
          SEP ().

Definition od_rot2_spec : ident * funspec :=
 DECLARE _od_rot2
  WITH p0: val, p1: val, t: Z, c0: Z, q0: Z, c1: Z, q1: Z, i0: Z, i1: Z
  PRE [ _p0 OF (tptr tint), _p1 OF (tptr tint), _t OF tint, _c0 OF tint, _q0 OF tint, _c1 OF tint, _q1 OF tint ]
          PROP  (Int.min_signed >>> 17 <= i0 <= Int.max_signed >>> 17; 0 <= c0 <= 65535; 0 <= q0 <= 15;
                 1 <<< q0 < c0;
                 Int.min_signed >>> 17 <=  t <= Int.max_signed >>> 17; 0 <= c1 <= 65535; 0 <= q1 <= 15;
                 1 <<< q1 < c1)
          LOCAL (temp _p0 p0; temp _p1 p1;
                 temp  _t (Vint (Int.repr  t));
                 temp _c0 (Vint (Int.repr c0)); temp _q0 (Vint (Int.repr q0));
                 temp _c1 (Vint (Int.repr c1)); temp _q1 (Vint (Int.repr q1)))
          SEP   (data_at Ews tint (Vint (Int.repr i0)) p0;
                 data_at Ews tint (Vint (Int.repr i1)) p1)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP (data_at Ews tint (Vint (Int.repr (od_mul_Z  t c1 q1))) p0;
               data_at Ews tint (Vint (Int.repr (od_mul_Z i0 c0 q0))) p1).

Definition _SUB : Z := 1.
Hint Unfold _SUB.
Definition _AVG : Z := 1.
Hint Unfold _AVG.

Definition od_rotate_pi4_kernel_sub_avg_Z :=
  fun (p0 p1 c0 q0 c1 q1: Z) =>
    let    t := od_sub_avg_Z p1 p0 in
    let p1_2 := od_mul_Z p0 c0 q0 in
    let p0_2 := od_mul_Z  t c1 q1 in
    let p1_3 := od_add_Z p1_2 p0_2 in
    (p0_2, p1_3).
Hint Unfold od_rotate_pi4_kernel_sub_avg_Z.

Definition od_rotate_pi4_kernel_sub_avg_spec : ident * funspec :=
 DECLARE _od_rotate_pi4_kernel
  WITH p0: val, p1: val, i0: Z, i1: Z, c0: Z, q0: Z, c1: Z, q1: Z, type: Z, avg: Z
  PRE [ _p0 OF (tptr tint), _p1 OF (tptr tint), _c0 OF tint, _q0 OF tint, _c1 OF tint, _q1 OF tint,
        _type OF tint, _avg OF tint ]
          PROP  (Int.min_signed >>> 17 <= i0 <= Int.max_signed >>> 17;
                 Int.min_signed >>> 17 <= i1 <= Int.max_signed >>> 17;
                 0 <= c0 <= 65535; 0 <= q0 <= 15; 1 <<< q0 < c0;
                 0 <= c1 <= 65535; 0 <= q1 <= 15; 1 <<< q1 < c1;
                 type = _SUB; avg = _AVG)
          LOCAL (temp _p0 p0; temp _p1 p1;
                 temp   _c0 (Vint (Int.repr   c0)); temp  _q0 (Vint (Int.repr  q0));
                 temp   _c1 (Vint (Int.repr   c1)); temp  _q1 (Vint (Int.repr  q1));
                 temp _type (Vint (Int.repr type)); temp _avg (Vint (Int.repr avg)))
          SEP   (data_at Ews tint (Vint (Int.repr i0)) p0;
                 data_at Ews tint (Vint (Int.repr i1)) p1)
  POST [ tvoid ] EX res: Z * Z,
          PROP (res = od_rotate_pi4_kernel_sub_avg_Z i0 i1 c0 q0 c1 q1)
          LOCAL ()
          SEP (data_at Ews tint (Vint (Int.repr (fst res))) p0;
               data_at Ews tint (Vint (Int.repr (snd res))) p1).


Definition od_fdct_2_Z :=
  fun (p0 p1: Z) =>
    let (p1_2, p0_2) := od_rotate_pi4_kernel_sub_avg_Z p1 p0 11585 13 11585 13 in
    (p0_2, p1_2).
Hint Unfold od_fdct_2_Z.

Definition od_fdct_2_spec : ident * funspec :=
 DECLARE _od_fdct_2
  WITH p0: val, p1: val, i0: Z, i1: Z(* , o0: Z, o1: Z *)
  PRE [ _p0 OF (tptr tint), _p1 OF (tptr tint) ]
          PROP  (0 <= i0 <= 8191; 0 <= i1 <= 8191)
          LOCAL (temp _p0 p0; temp _p1 p1)
          SEP   (data_at Ews tint (Vint (Int.repr i0)) p0;
                 data_at Ews tint (Vint (Int.repr i1)) p1)
  POST [tvoid] EX res: Z * Z,
          PROP (res = od_fdct_2_Z i0 i1;
                  -32768 <= (fst res) <= 32767; -32768 <= (snd res) <= 32767)
          LOCAL ()
          SEP (data_at Ews tint (Vint (Int.repr (fst res))) p0;
               data_at Ews tint (Vint (Int.repr (snd res))) p1).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ]
     PROP ()
     LOCAL ()
     SEP(TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    od_add_spec; od_sub_spec; od_add_avg_spec; od_sub_avg_spec; od_mul_spec; od_rot2_spec;
    od_rotate_pi4_kernel_sub_avg_spec; od_fdct_2_spec; main_spec
  ]).

Lemma div2_le: forall m, m <= 0 -> m <= Z.div2 m.
  intros.
  rewrite Z.div2_div.
  apply Z.div_le_lower_bound; omega.
Qed.

Lemma div2_le_zero: forall m, m <= 0 -> Z.div2 m <= 0.
  intros.
  destruct (Z_le_lt_eq_dec _ _ H).
  rewrite <- (Z.div2_neg m) in l.
  omega.
  rewrite e.
  simpl.
  omega.
Qed.

Theorem div_le_lower_bound_neg:
  forall a b q, a<=0 -> 0<b -> b*q <= a -> q <= a/b.
Proof.
  intros a b q Ha Hb H.
  destruct (Z.lt_ge_cases 0 q).
  rewrite <- (Z.div_mul q b); try Z.order.
  apply Z.div_le_mono; auto.
  rewrite Z.mul_comm; auto.

  assert(a/b <= 0).
  apply Z.div_le_upper_bound; omega.
  apply Z.div_le_lower_bound; omega.
Qed.

Theorem div_le_upper_bound_neg:
  forall a b q, a<=0 -> 0<b -> a <= b*q -> a/b <= q.
Proof.
  intros.
  rewrite (Z.mul_le_mono_pos_l _ _ b) by Z.order.
  apply Z.le_trans with a; auto.
  apply Z.mul_div_le; auto.
Qed.

Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r ->
                                     p/r <= p/q.
Proof.
  intros p q r Hp (Hq,Hqr).
  apply Z.div_le_lower_bound; auto.
  rewrite (Z.div_mod p r) at 2 by Z.order.
  apply Z.le_trans with (r*(p/r))%Z.
  apply Z.mul_le_mono_nonneg_r; try Z.order.
  apply Z.div_pos ; Z.order.
  rewrite <- (Z.add_0_r (r*(p/r))) at 1.
  rewrite <- Z.add_le_mono_l. destruct (Z.mod_bound_pos p r); Z.order.
Qed.

Lemma div_le_compat_l_neg: forall p q r, p<=0 -> 0<q<=r -> p/q <= p/r.
Proof.
  intros p q r Hp (Hq,Hqr).
  apply div_le_lower_bound_neg; try omega.
  rewrite (Z.div_mod p q) at 2 by Z.order.
  apply Z.le_trans with (q*(p/q))%Z.
  apply Z.mul_le_mono_nonpos_r; try omega.
  apply div_le_upper_bound_neg; try omega.
  rewrite <- Z.add_0_r at 1.
  apply Zplus_le_compat_l.
  apply Z.mod_pos_bound; Z.order.
Qed.

Lemma shiftl_neg_le: forall m p q, m < 0 -> p >= 0 -> q >= 0 -> p <= q -> (m <<< q) <= (m <<< p).
  intros.
  repeat rewrite Z.shiftl_mul_pow2; try omega.
  apply Z.mul_le_mono_nonpos_l; try omega.
  apply Z.pow_le_mono_r; omega.
Qed.

Lemma shiftr_neg_le: forall m p q, m < 0 -> p >= 0 -> q >= 0 -> p <= q -> (m >>> p) <= (m >>> q).
  intros.
  repeat rewrite Z.shiftr_div_pow2; try omega.
  apply div_le_compat_l_neg.
  omega.
  split.
  apply Z.lt_le_trans with (2^0).
  simpl. omega.
  apply Z.pow_le_mono_r; omega.
  apply Z.pow_le_mono_r; omega.
Qed.

Lemma shiftl_mono_l: forall a b q, 0 <= q -> a <= b -> a <<< q <= b <<< q.
  intros.
  repeat rewrite Z.shiftl_mul_pow2; try omega.
  apply Z.mul_le_mono_pos_r; try omega.
  apply Z.pow_pos_nonneg; omega.
Qed.

Lemma shiftl_mono_r: forall m p q, m > 0 -> p <= q -> (m <<< p) <= (m <<< q).
  intros.
  destruct p, q;
    repeat rewrite (Z.shiftl_mul_pow2 _ 0);
    repeat rewrite (Z.shiftl_mul_pow2 _ (Z.pos _));
    repeat rewrite (Z.shiftl_div_pow2 _ (Z.neg _));
    repeat rewrite Pos2Z.opp_neg;
    try easy.
  apply Z.mul_le_mono_nonneg_l; try omega.
  apply Z.pow_le_mono_r; omega.
  apply Z.mul_le_mono_nonneg_l; try omega.
  apply Z.pow_le_mono_r; omega.

  apply Z.le_trans with m.
  apply Z.div_le_upper_bound.
  apply Z.pow_pos_nonneg; try omega; auto.
  replace m with (1*m)%Z at 1 by omega.
  apply Z.mul_le_mono_nonneg_r; try omega.
  replace 1 with (Z.succ 0) by omega.
  apply Zlt_le_succ.
  apply Z.pow_pos_nonneg; try omega; auto.
  simpl; omega.

  apply Z.le_trans with m.
  apply Z.div_le_upper_bound.
  apply Z.pow_pos_nonneg; try omega; auto.
  replace m with (1*m)%Z at 1 by omega.
  apply Z.mul_le_mono_nonneg_r; try omega.
  replace 1 with (Z.succ 0) by omega.
  apply Zlt_le_succ.
  apply Z.pow_pos_nonneg; try omega; auto.

  replace m with (m*1)%Z at 1 by omega.
  apply Z.mul_le_mono_nonneg_l; try omega.
  replace 1 with (Z.succ 0) by omega.
  apply Zlt_le_succ.
  apply Z.pow_pos_nonneg; try omega; auto.

  apply Z.div_le_compat_l; try omega.
  split.
  apply Z.pow_pos_nonneg; try omega; auto with zarith.
  apply Z.pow_le_mono_r; try omega.
  apply Z.opp_le_mono.
  auto.
Qed.

Lemma shiftr_mono_l: forall a b q, 0 <= q -> a <= b -> a >>> q <= b >>> q.
  intros.
  repeat rewrite Z.shiftr_div_pow2; try omega.
  apply Z.div_le_mono.
  apply Z.pow_pos_nonneg; omega.
  trivial.
Qed.

Lemma shiftr_pos_nonneg: forall a b, 0 <= a -> 0 <= b -> 0 <= a >>> b.
  intros.
  rewrite Z.shiftr_div_pow2; try omega.
  apply Z.div_pos; try omega.
  apply Z.pow_pos_nonneg; omega.
Qed.
Lemma shiftl_pos_nonneg: forall a b, 0 <= a -> 0 <= b -> 0 <= a <<< b.
  intros.
  rewrite Z.shiftl_mul_pow2; try omega.
  apply Z.mul_nonneg_nonneg; try omega.
  apply Z.lt_le_incl.
  apply Z.pow_pos_nonneg; omega.
Qed.

Lemma shr_round_neg_mono_r: forall x a b, 0 <= a <= b -> x + (1 <<< b) < 0 ->
                                          od_shr_round_Z x a <= od_shr_round_Z x b.
  intros.
  autounfold.
  apply Z.le_trans with (x + (1 <<< a >>> 1) >>> b).
  apply shiftr_neg_le; try omega.
  apply Z.le_lt_trans with (x + (1 <<< b)); try auto.
  apply Z.add_le_mono_l.
  apply Z.le_trans with (1 <<< a).
  rewrite <- Z.div2_spec.
  rewrite Z.div2_div.
  apply Z.div_le_upper_bound; try omega.
  rewrite <- Z.mul_1_l at 1.
  apply Z.mul_le_mono_nonneg_r; try omega.
  apply Z.shiftl_nonneg; omega.
  repeat rewrite Z.shiftl_mul_pow2; try omega.
  repeat rewrite Z.mul_1_l.
  apply Z.pow_le_mono_r; omega.
  apply shiftr_mono_l; try omega.
  apply Z.add_le_mono_l.
  apply shiftr_mono_l; try omega.
  apply shiftl_mono_r; omega.
Qed.

Lemma shr_round_mono_l: forall x y a, x <= y -> a >= 0 ->
                                      od_shr_round_Z x a <= od_shr_round_Z y a.
  intros.
  autounfold.
  apply shiftr_mono_l; omega.
Qed.

(* TOOO: only needs _ <= _, not _ <= _ <= _ *)
Lemma shr_round_neg_le: forall x q min_q max_q: Z, min_q >= 0 -> x + (1 <<< max_q) < 0 ->
                                                   min_q <= q <= max_q ->
                                                   od_shr_round_Z x min_q <= od_shr_round_Z x q <= od_shr_round_Z x max_q.
  intros.
  split; apply shr_round_neg_mono_r; try omega.
  apply Z.le_lt_trans with (x + (1 <<< max_q)); try omega.
  apply Z.add_le_mono_l.
  apply shiftl_mono_r; omega.
Qed.

Lemma shr_round_pos_le: forall x a b: Z, 0 <= x -> 0 <= a <= b ->
                                         1 <<< (b - 1) <= x ->
                                         od_shr_round_Z x b <= od_shr_round_Z x a.
  intros.
  autounfold.
  destruct H0.
(*Z_div_plus: forall a b c : Z, c > 0 -> (a + b * c) / c = a / c + b
Zdiv_mult_le: forall a b c : Z, 0 <= a -> 0 <= b -> 0 <= c -> c * (a / b) <= c * a / b
 *)

  destruct (Z_le_lt_eq_dec _ _ H2).
  Focus 2. repeat rewrite <- e; reflexivity.

  apply Z.le_trans with ((2*x) >>> b).
  - apply shiftr_mono_l; try omega.
    rewrite Z.shiftr_shiftl_l; omega.
  - apply Z.le_trans with (x >>> a).
    + repeat rewrite Z.shiftr_div_pow2; try omega.
      replace (2^b) with (2*(2^(b-1)))%Z.
      rewrite Z.div_mul_cancel_l; try omega.
      apply Z.div_le_compat_l; try omega.
      split.
      apply Z.pow_pos_nonneg; omega.
      apply Z.pow_le_mono_r; omega.
      assert (0 < 2^(b-1)) by (apply Z.pow_pos_nonneg; omega).
      omega.

      rewrite <- Z.pow_succ_r; try omega.
      rewrite <- Z.add_1_r.
      replace (b - 1 + 1) with b by omega.
      reflexivity.
    + apply shiftr_mono_l; try omega.
      replace x with (x+0) at 1 by (apply Z.add_0_r).
      apply Z.add_le_mono_l.
      apply shiftr_pos_nonneg; try omega.
      apply shiftl_pos_nonneg; omega.
Qed.

Lemma range_mul_rzero: forall a b min_a max_a min_b max_b: Z, min_a <= a <= max_a -> min_b <= b <= max_b ->
                                                              0 <= min_b -> min_a <= 0 ->  0 <= max_a ->
                                                              min_a*max_b <= a*b <= max_a*max_b.
  intros.
  split.
  - apply Z.le_trans with (min_a*b)%Z.
    apply Z.mul_le_mono_nonpos_l; omega.
    apply Zmult_le_compat_r; omega.
  - apply Z.le_trans with (max_a*b)%Z.
    apply Z.mul_le_mono_nonneg_r; omega.
    apply Zmult_le_compat_l; omega.
Qed.

Lemma range_sub: forall a b min_a max_a min_b max_b: Z, min_a <= a <= max_a -> min_b <= b <= max_b ->
                                                        min_a-max_b <= a-b <= max_a-min_b.
  intros.
  omega.
Qed.

Lemma range_add: forall a b min_a max_a min_b max_b: Z, min_a <= a <= max_a -> min_b <= b <= max_b ->
                                                        min_a+min_b <= a+b <= max_a+max_b.
  intros.
  omega.
Qed.

Lemma range_sub_avg: forall a b min_a max_a min_b max_b: Z, min_a <= a <= max_a -> min_b <= b <= max_b ->
                                                            od_sub_avg_Z min_a max_b <= od_sub_avg_Z a b <= od_sub_avg_Z max_a min_b.
  intros.
  repeat unfold od_sub_avg_Z.
  repeat unfold od_sub_Z.
  split; apply shiftr_mono_l; omega.
Qed.

(*od_mul_Z (od_sub_avg_Z i1 i0) c1 q1*)

Ltac range t :=
  let set_goal := (fun _ =>
                     let min_t  := fresh "min_t" in
                     let max_t  := fresh "max_t" in
                     evar (min_t: Z); evar (max_t: Z);
                     let min_t' := eval unfold min_t in min_t in
                         let max_t' := eval unfold max_t in max_t in
                             (* clear min_t max_t; *)
                             assert (min_t' <= t <= max_t')
                  ) in
  match t with
  | Z0 =>
    idtac
  | Zpos _ =>
    idtac
  | Zneg _ =>
    idtac
  | (?a + ?b)%Z =>
    range a;
    range b;
    set_goal ();
    only 1: (eapply range_add; try easy)
  | (?a - ?b)%Z =>
    range a;
    range b;
    set_goal ();
    only 1: (eapply range_sub; try easy)
  | (od_sub_avg_Z ?a ?b)%Z =>
    range a;
    range b;
    set_goal ();
    only 1: (eapply range_sub_avg; try easy)
  | (?a * ?b)%Z =>
    range a;
    range b;
    set_goal ();
    only 1: (eapply range_mul_rzero; try easy)
  | _ =>
    match goal with
    | [ Hx: ?min_t <= t <= ?max_t |- _ ] =>
      idtac
    | _ =>
      set_goal ()
    end
  end.

Ltac range_left :=
  match goal with
  | [ |- ?x <= _ ] =>
    range x
  end.

Ltac range_middle :=
  match goal with
  | [ |- _ <= ?x <= _ ] =>
    range x
  end.

Ltac range_right :=
  match goal with
  | [ |- _ <= ?x ] =>
    range x
  end.

Lemma body_od_fdct_2: semax_body Vprog Gprog f_od_fdct_2 od_fdct_2_spec.
Proof.
  start_function.
  forward_call (p1, p0, i1, i0, 11585, 13, 11585, 13, _SUB, _AVG).

  Focus 2.
  apply extract_exists_pre; intro; forward.
  remember (od_fdct_2_Z i0 i1) as res.
  Exists res.
  entailer!.
  (*TODO: od_fdct_2_Z bounds properties *)
  simpl.
  unfold od_add_Z, od_mul_Z.
  autounfold. autounfold. simpl.
  replace (8192 >>> 1) with 4096 by easy.

  rewrite !Z.shiftr_div_pow2; try omega.
  replace (2^1) with 2 by easy.
  replace (2^13) with 8192 by easy.
  remember ((i0 - i1) / 2) as i01div.
  remember (i1 * 11585 + 4096)%Z as a.
  remember (i01div * 11585 + 4096) as b.
  remember (a / 8192) as adiv.
  remember (b / 8192) as bdiv.

  assert (2*i01div <= (i0 - i1) < 2*(Z.succ i01div)).
  rewrite Heqi01div.
  split.
  apply Z.mul_div_le; easy.
  apply Z.mul_succ_div_gt; easy.

  assert (8192*adiv <= a < 8192*(Z.succ adiv)).
  rewrite Heqadiv.
  split.
  apply Z.mul_div_le; easy.
  apply Z.mul_succ_div_gt; easy.

  assert (8192*bdiv <= b < 8192*(Z.succ bdiv)).
  rewrite Heqbdiv.
  split.
  apply Z.mul_div_le; easy.
  apply Z.mul_succ_div_gt; easy.

  omega.

  rewrite !Z.shiftr_div_pow2; try omega.
  assert (Hmin: Int.min_signed / 2^17 <= 0).
  apply Z.div_le_upper_bound; easy.


  remember (Int.max_signed / 2^17) as max_signed_div.
  assert (Int.max_signed < (2^17)*(Z.succ max_signed_div)).
  rewrite Heqmax_signed_div.
  apply Z.mul_succ_div_gt; easy.
  assert (8191 < max_signed_div). rewrite Heqmax_signed_div. easy.

  split.
  split.
  apply Z.le_trans with 0; easy.
  omega.
  split.
  split.
  apply Z.le_trans with 0; easy.
  omega.
  easy.
Qed.

Lemma body_od_add: semax_body Vprog Gprog f_od_add od_add_spec.
Proof.
  start_function.
  forward.
  entailer!.

  unfold Z.shiftr in *.
  simpl in *.
  repeat rewrite Int.signed_repr.

  repable_signed.
  repable_signed.
  repable_signed.
Qed.

Lemma body_od_sub: semax_body Vprog Gprog f_od_sub od_sub_spec.
Proof.
  start_function.
  forward.
  entailer!.

  unfold Z.shiftr in *.
  simpl in *.
  repeat rewrite Int.signed_repr.

  repable_signed.
  repable_signed.
  repable_signed.
Qed.

Lemma shr_signed: forall m n,
    Int.min_signed <= m <= Int.max_signed ->
    0 <= n <= Int.max_unsigned ->
    Int.repr (m >>> n) = Int.shr (Int.repr m) (Int.repr n).
  intros.
  unfold Int.shr.
  f_equal.
  rewrite Int.signed_repr, Int.unsigned_repr; auto.
Qed.

Lemma body_od_add_avg: semax_body Vprog Gprog f_od_add_avg od_add_avg_spec.
Proof.
  start_function.
  forward_call (p0, p1).

  assert(sum_signed: Int.min_signed <= p0 + p1 <= Int.max_signed).
    unfold Z.shiftr in *.
    simpl in *.
    repable_signed.

  forward.
  entailer!.
  f_equal.
  unfold Int.shr.
  rewrite Int.signed_repr.
  auto.
  auto.

  unfold od_add_avg_Z.
  entailer!.
  f_equal.
  unfold Int.shr.
  normalize.
  rewrite Int.signed_repr.
  trivial.
  trivial.
Qed.

Lemma body_od_sub_avg: semax_body Vprog Gprog f_od_sub_avg od_sub_avg_spec.
Proof.
  start_function.
  forward_call (p0, p1).

  assert(sum_signed: Int.min_signed <= p0 - p1 <= Int.max_signed). {
    unfold Z.shiftr in *.
    simpl in *.
    repable_signed.
  }

  unfold od_sub_avg_Z. unfold od_sub_Z.
  forward.
  entailer!.
  rewrite <- shr_signed; try repable_signed.
  auto.
Qed.

Lemma body_od_mul: semax_body Vprog Gprog f_od_mul od_mul_spec.
Proof.
  start_function.

  assert(ltu_q_wordsize: Int.ltu (Int.repr q) Int.iwordsize = true). {
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
  }

  assert (pow2_q_signed: Int.min_signed <= 1 <<< q <= Int.max_signed). {
    split.
    - apply Z.le_trans with (1 <<< 0).
      simpl.
      repable_signed.
      apply shiftl_mono_r; omega.
    - apply Z.le_trans with (1 <<< 15).
      apply shiftl_mono_r; omega.
      unfold Int.max_signed; simpl; omega.
  }

  rewrite !Z.shiftr_div_pow2 in H; try omega.
  remember (Int.min_signed / 2^17) as min_signed_div.
  assert ((2^17)*min_signed_div <= Int.min_signed). {
    rewrite Heqmin_signed_div.
    apply Z.mul_div_le; easy.
  }
  remember (Int.max_signed / 2^17) as max_signed_div.
  assert ((2^17)*max_signed_div <= Int.max_signed < (2^17)*(Z.succ max_signed_div)). {
    rewrite Heqmax_signed_div.
    split.
    - apply Z.mul_div_le; easy.
    - apply Z.mul_succ_div_gt; easy.
  }

  remember (1 <<< q >>> 1) as bias.
  assert (Hq: 0 <= bias <= 2^14). {
    rewrite Heqbias.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by omega.
    replace (1 * 2^q)%Z with (2^q) by omega.
    split.
    - apply Z.div_le_lower_bound.
      replace (2^1) with 2 by easy.
      omega.
      simpl.
      apply Z.lt_le_incl.
      apply Z.pow_pos_nonneg; omega.
    - destruct H1.
      destruct (Z_le_lt_eq_dec _ _ H1).
      + rewrite <- Z.pow_sub_r by omega.
        apply Z.pow_le_mono_r; omega.
      + rewrite <- e.
        easy.
  }
  replace (2^14) with 16384 in Hq by easy.

  range (n*c)%Z. rewrite Heqmin_signed_div; easy. rewrite Heqmax_signed_div; easy.
  assert (Hnc1: Int.min_signed <= n*c <= Int.max_signed). {
    split.
    apply Z.le_trans with min_t; unfold min_t; rewrite Heqmin_signed_div. easy. omega.
    apply Z.le_trans with max_t; unfold max_t; rewrite Heqmax_signed_div. omega. easy.
  }
  assert (Hnc2: Int.min_signed <= n*c + bias <= Int.max_signed). {
    split.
    omega.

    replace (2^17) with 131072 in * by easy.

    unfold Int.max_signed in *; simpl in *. omega.
  }

  forward.
  entailer!.

  (* Bug? These definitions seem to be lost by "forward." and "entailer!." *)
  remember (Int.min_signed / 2^17) as min_signed_div.
  assert ((2^17)*min_signed_div <= Int.min_signed). {
    rewrite Heqmin_signed_div.
    apply Z.mul_div_le; easy.
  }
  remember (Int.max_signed / 2^17) as max_signed_div.
  assert ((2^17)*max_signed_div <= Int.max_signed < (2^17)*(Z.succ max_signed_div)). {
    rewrite Heqmax_signed_div.
    split.
    - apply Z.mul_div_le; easy.
    - apply Z.mul_succ_div_gt; easy.
  }

  split3.
  {
    rewrite ltu_q_wordsize.
    unfold is_true. trivial.
  }
  {
    rewrite ltu_q_wordsize.
    unfold is_true. trivial.
  }
  {
    rewrite !Int.signed_repr; try omega.

    repable_signed.
    split.
    apply Z.le_trans with min_signed_div.
    rewrite Heqmin_signed_div. easy. omega.
    apply Z.le_trans with max_signed_div.
    omega. rewrite Heqmax_signed_div. easy.
  }

  (* Bug? These definitions seem to be lost by "forward." and "entailer!." *)
  remember (Int.min_signed / 2^17) as min_signed_div.
  assert ((2^17)*min_signed_div <= Int.min_signed). {
    rewrite Heqmin_signed_div.
    apply Z.mul_div_le; easy.
  }
  remember (Int.max_signed / 2^17) as max_signed_div.
  assert ((2^17)*max_signed_div <= Int.max_signed < (2^17)*(Z.succ max_signed_div)). {
    rewrite Heqmax_signed_div.
    split.
    - apply Z.mul_div_le; easy.
    - apply Z.mul_succ_div_gt; easy.
  }

  unfold sem_shift. simpl.
  rewrite ltu_q_wordsize.
  simpl.
  entailer!.
  unfold Int.shr, Int.shl.
  rewrite !Int.unsigned_repr by repable_signed.
  rewrite !Int.signed_repr.
  omega.
  omega.
  rewrite !Int.signed_repr.
  repable_signed.
  omega.

  entailer!.
  unfold sem_shift. simpl.
  rewrite ltu_q_wordsize.
  simpl.
  rewrite ltu_q_wordsize.
  simpl.
  unfold Int.shl, Int.shr.
  rewrite add_repr.
  rewrite !Int.unsigned_repr; try repable_signed.
  rewrite !Int.signed_repr.
  f_equal.
  omega.
  rewrite !Int.signed_repr.
  split.
  omega.
  omega.
  omega.
Qed.

Lemma body_od_rot2: semax_body Vprog Gprog f_od_rot2 od_rot2_spec.
Proof.
  start_function.
  forward.
  forward_call (i0, c0, q0).
  forward.
  forward_call (t, c1, q1).
  forward.
  forward.
Qed.

Lemma body_od_rotate_pi4_kernel_sub_avg: semax_body Vprog Gprog f_od_rotate_pi4_kernel od_rotate_pi4_kernel_sub_avg_spec.
Proof.
  start_function.
  remember (od_sub_avg_Z i1 i0) as t.
  (** After the if, t = od_sub_avg(\*p1, \*p0) **)
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
                  forward_if (PROP() (LOCALx (temp _t'1 (Vint (Int.repr t)) :: Q) (SEPx R))) end.
  (* `type == ADD` is never true. *)
  contradict H9.
  rewrite H7.
  unfold _SUB.
  computable.
  forward_if. (* avg ? ... *)
  (* od_sub_avg(\*p1, \*p0) *)
  forward.
  forward.
  forward_call (i1, i0).
  (* Int.min_signed >>> 1 <= i1 <= Int.max_signed >>> 1 /\ Int.min_signed >>> 1 <= i0 <= Int.max_signed >>> 1 *)
  unfold Z.shiftr in *. simpl in *.
  repeat split; omega.
  forward.
  forward.
  entailer!.
  (* `avg` islways false. *)
  contradict H10.
  rewrite H8.
  unfold _AVG.
  unfold Int.zero.
  computable.

  forward. (* _t = _t'1 *)
  forward_call (p0, p1, t, c0, q0, c1, q1, i0, i1).
  unfold Z.shiftr in *. simpl in *.
  rewrite Heqt.
  (* Hide expression so that it doesn't get split *)
  remember (-16384 <= od_sub_avg_Z i1 i0 <= 16383) as sub_bounds.
  repeat split; try omega.
  rewrite Heqsub_bounds.
  replace (-16384) with (-16383 - 1) by omega.
  apply od_sub_avg_bounded with (max := 16383); omega.

  remember (od_mul_Z t c1 q1) as p0_2.
  remember (od_mul_Z i0 c0 q0) as p1_2.
  remember (od_add_Z p1_2 p0_2) as p1_3.
  (** After the if, \*p1 = od_add(\*p1, \*p0) **)
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
                  forward_if (PROP() (LOCALx (temp _t'8 (Vint (Int.repr p1_3)) :: Q) (SEPx R))) end.
  (* `type == ADD` is never true. *)
  contradict H9.
  rewrite H7.
  unfold _SUB.
  computable.

  forward.
  forward.
  forward_call (p1_2, p0_2).

  range (i0*c0)%Z.

  split.

  (* Int.min_signed >>> 1 <= p1_2 <= Int.max_signed >>> 1 *)
  rewrite Heqp1_2.
  unfold od_mul_Z.

  split.
  apply Z.le_trans with (od_shr_round_Z ((Int.min_signed >>> 17) * 65535) q0).
  apply Z.le_trans with (od_shr_round_Z ((Int.min_signed >>> 17) * 65535) 0).
  easy.
  apply shr_round_neg_mono_r; try omega.
  apply Z.le_lt_trans with ((Int.min_signed >>> 17) * 65535 + (1 <<< 15)).
  apply Z.add_le_mono_l.
  apply shiftl_mono_r; omega.
  easy.
  apply shr_round_mono_l; omega.

  apply Z.le_trans with (od_shr_round_Z ((Int.max_signed >>> 17) * 65535) q0).
  apply shr_round_mono_l; omega.
  apply Z.le_trans with (od_shr_round_Z ((Int.max_signed >>> 17) * 65535) 0).
  apply shr_round_pos_le; try omega.
  simpl; omega.
  apply Z.le_trans with (1 <<< 14).
  apply shiftl_mono_r; try omega.
  simpl; omega.
  easy.

  (* Int.min_signed >>> 1 <= p0_2 <= Int.max_signed >>> 1 *)
  rewrite Heqp0_2.
  rewrite Heqt.

  unfold od_mul_Z.
  range ((od_sub_avg_Z i1 i0) * c1)%Z.
  split.
  apply Z.le_trans with (od_shr_round_Z min_t1 q1).
  apply Z.le_trans with (od_shr_round_Z min_t1 0).
  easy.
  apply shr_round_neg_mono_r; try omega.
  apply Z.le_lt_trans with (min_t1 + (1 <<< 15)).
  apply Z.add_le_mono_l.
  apply shiftl_mono_r; omega.
  easy.
  apply shr_round_mono_l; unfold min_t1; omega.

  apply Z.le_trans with (od_shr_round_Z max_t1 q1).
  apply shr_round_mono_l; unfold max_t1; omega.
  apply Z.le_trans with (od_shr_round_Z max_t1 0).
  apply shr_round_pos_le; unfold max_t1; try omega.
  simpl; omega.
  apply Z.le_trans with (1 <<< 14).
  apply shiftl_mono_r; omega.
  simpl; omega.
  easy.

  forward.
  entailer!.

  forward. forward.
  remember (od_rotate_pi4_kernel_sub_avg_Z i0 i1 c0 q0 c1 q1) as res.
  Exists res.
  entailer!.
Qed.


Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
