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
  WITH p0: val, p1: val, c0: Z, q0: Z, c1: Z, q1: Z, i0: Z, i1: Z, type: Z, avg: Z
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
    sumtwo_spec; od_add_spec; od_add_avg_spec; od_sub_avg_spec; od_mul_spec; od_rot2_spec;
    od_rotate_pi4_kernel_sub_avg_spec; od_fdct_2_spec
  ]).

Lemma add_le_2: forall min max a b: Z, Zeven min ->
                                       min < 0                   -> max > 0 ->
                                       min >>> 1 <= a <= max >>> 1 -> min >>> 1 <= b <= max - (max >>> 1) ->
                                       min <= a + b <= max.
  intros.
  split.
  replace min with ((min >>> 1) + (min >>> 1)).
  apply Z.add_le_mono; omega.
  symmetry.
  rewrite Z.add_diag.
  unfold Z.shiftr.
  simpl.
  apply Zeven_div2.
  trivial.

  (* destruct Zeven_odd_dec with max. *)
  (* - replace max with ((max >>> 1) + (max >>> 1)) in H3 |- *. *)
  (*   apply Z.add_le_mono. *)
  (*   unfold Z.shiftr in *. *)

  (*   apply Z.add_le_mono; omega. *)
  (*   rewrite Z.add_diag. *)
  (*   unfold Z.shiftr. *)
  (*   simpl. *)
  (*   symmetry. *)
  (*   apply Zeven_div2. *)
  (*   trivial. *)
  (* - replace max with ((max >>> 1) + (max >>> 1) + 1). *)
  (*   apply Z.le_trans with ((max >>> 1) + (max >>> 1)). *)
  (*   apply Z.add_le_mono; omega. *)
  (*   omega. *)
  (*   rewrite Z.add_diag. *)
  (*   unfold Z.shiftr. *)
  (*   simpl. *)
  (*   symmetry. *)
  (*   apply Zodd_div2. *)
  (*   trivial. *)
  admit.
Admitted.

Lemma body_od_add: semax_body Vprog Gprog f_od_add od_add_spec.
Proof.
  start_function.
  forward.
  entailer!.

  unfold Z.shiftr in *.
  simpl in *.

  repeat rewrite Int.signed_repr.
  apply add_le_2; try easy.
  unfold Int.max_signed, Int.min_signed.
  simpl.
  replace (-2147483648 >>> 1) with (-1073741824) by auto.
  omega.
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
  apply add_le_2; try easy.
  unfold Int.max_signed, Int.min_signed.
  simpl.
  replace (-2147483648 >>> 1) with (-1073741824) by auto.
  omega.
  repable_signed.
  repable_signed.
Qed.

Lemma body_od_add_avg: semax_body Vprog Gprog f_od_add_avg od_add_avg_spec.
Proof.
  start_function.
  forward_call (p0, p1).

  assert(sum_signed: Int.min_signed <= p0 + p1 <= Int.max_signed).
    unfold Z.shiftr in *.
    simpl in *.
    apply add_le_2; try (easy || repable_signed).
    unfold Int.max_signed, Int.min_signed.
    simpl.
    replace (-2147483648 >>> 1) with (-1073741824) by auto.
    omega.

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

Lemma conj_same: forall P: Prop, P -> P /\ P.
  intros.
  split; trivial.
Qed.

Lemma shiftl_mono_r: forall m p q, m > 0 -> p >= 0 -> q >= 0 -> p <= q -> (m <<< p) <= (m <<< q).
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
    Int.repr (m >>> n) = Int.shr (Int.repr m) (Int.repr n).
  intros.
  unfold Int.shr.
  f_equal.
  rewrite Int.signed_repr, Int.unsigned_repr; auto.
Qed.

Lemma body_od_mul: semax_body Vprog Gprog f_od_mul od_mul_spec.
Proof.
  start_function.
  admit.

  (* assert(ltu_q_wordsize: Int.ltu (Int.repr q) Int.iwordsize = true). *)
  (*   unfold Int.ltu. *)
  (*   rewrite zlt_true. *)
  (*   simpl. *)
  (*   trivial. *)

  (*   unfold Int.iwordsize. *)
  (*   unfold Int.zwordsize. *)
  (*   simpl. *)
  (*   repeat rewrite Int.unsigned_repr. *)
  (*   omega. *)
  (*   repable_signed. *)
  (*   repable_signed. *)

  (* assert (pow2_q_signed: Int.min_signed <= 1 <<< q <= Int.max_signed). *)
  (*   split. *)
  (*   (**) apply Z.le_trans with (1 <<< 0). *)
  (*     simpl. *)
  (*     repable_signed. *)
  (*     apply shiftl_mono_r; omega. *)
  (*   (**) apply Z.le_trans with (1 <<< 15). *)
  (*     apply shiftl_mono_r; omega. *)
  (*     unfold Int.max_signed; simpl; omega. *)


  (* forward. *)
  (* entailer!. *)
  (* split3. *)
  (* rewrite ltu_q_wordsize. *)
  (* unfold is_true. trivial. *)
  (* rewrite ltu_q_wordsize. *)
  (* unfold is_true. trivial. *)
  (* admit. (*Int.min_signed <= Int.signed (Int.repr n) * Int.signed (Int.repr c) <= Int.max_signed*) *)

  (* admit. *)
  (* admit. *)

  (* entailer!. *)
  (* unfold sem_shift, sem_shift_ii. *)
  (* simpl. *)
  (* rewrite ltu_q_wordsize. *)
  (* simpl. *)
  (* f_equal. *)

  (* (* Lemma add_signed: forall m n, *) *)
  (* (*     (* Int.min_signed <= m <= Int.max_signed -> *) *) *)
  (* (*     (* 0 <= n <= Int.max_unsigned -> *) *) *)
  (* (*     Int.repr (m + n) = Int.shr (Int.repr m) (Int.repr n). *) *)

  (* unfold od_mul_Z. *)
  (* rewrite shr_signed. *)
  (* f_equal. *)
  (* rewrite Int.add_signed. *)
  (* f_equal. *)
  (* repeat rewrite Int.signed_repr. *)
  (* f_equal. *)

  (* unfold Int.shr, Int.shl. *)
  (* repeat rewrite Int.signed_repr, Int.unsigned_repr; try repable_signed. *)
  (* rewrite Int.unsigned_repr. *)
  (* normalize. repable_signed. *)
  (* normalize. *)

  (* (* Int.min_signed <= 1 <<< q >>> 1 <= Int.max_signed *) *)
  (* split. *)
  (* (**)  apply Z.le_trans with ((1 <<< 0) >>> 1). *)
  (*   unfold Int.min_signed, Z.shiftr; simpl; omega. *)
  (*   repeat rewrite Z.shiftr_div_pow2. *)
  (*   simpl. *)
  (*   unfold Z.pow_pos. simpl. *)
  (*   apply Z.div_le_mono. *)
  (*   omega. *)
  (*   apply Z.le_trans with (1 <<< 0). *)
  (*   simpl. omega. *)
  (*   apply shiftl_mono_r; omega. *)
  (*   omega. *)
  (*   omega. *)
  (* (**) apply Z.le_trans with ((1 <<< 15) >>> 1). *)
  (*   repeat rewrite Z.shiftr_div_pow2. *)
  (*   apply Z.div_le_mono. *)
  (*   simpl. *)
  (*   unfold Z.pow_pos. simpl. *)
  (*   omega. *)
  (*   apply shiftl_mono_r; omega. *)
  (*   omega. *)
  (*   omega. *)
  (*   unfold Int.max_signed, Z.shiftr; simpl; omega. *)
  (*   normalize. *)

  (* split. *)
  (* (**) admit. *)
  (* (**) admit. *)
  (* split. *)
  (* (**) admit. *)
  (* (**) admit. *)

  (* split; repable_signed. *)
Admitted.

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

Lemma shiftr_mono_l: forall a b q, 0 <= q -> a <= b -> a >>> q <= b >>> q.
  intros.
  repeat rewrite Z.shiftr_div_pow2; try omega.
  apply Z.div_le_mono.
  apply Z.pow_pos_nonneg; omega.
  trivial.
Qed.

Lemma shr_round_mono_r: forall x a b, 0 <= a <= b -> x + (1 <<< b) < 0 ->
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

Lemma shr_round_neg_le: forall x q min_q max_q: Z, min_q >= 0 -> x + (1 <<< max_q) < 0 ->
                                                   min_q <= q <= max_q ->
                                                   od_shr_round_Z x min_q <= od_shr_round_Z x q <= od_shr_round_Z x max_q.
  intros.
  split.
  - apply shr_round_mono_r; try omega.
    apply Z.le_lt_trans with (x + (1 <<< max_q)); try omega.
    apply Z.add_le_mono_l.
    apply shiftl_mono_r; omega.
  - apply shr_round_mono_r; omega.
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
  split.
  rewrite Heqp1_2.
  unfold od_mul_Z.


  repeat rewrite Int.Zshiftl_mul_two_p in * by omega.
  repeat rewrite Int.Zshiftr_div_two_p in * by omega.
  (* Hint Unfold two_p. *)
  (* Hint Unfold two_power_pos. *)
  (* Hint Unfold shift_pos. *)
  destruct q0; replace (two_p 1) with 2 by auto; simpl;
    replace (1/2) with 0 by auto; try rewrite Zdiv_1_r; try rewrite Z.add_0_r; try rewrite Z.mul_0_r; try rewrite Zdiv_0_r.

  (* autounfold; destruct q0; *)
  (*   replace (two_p 1) with 2 by auto; *)
  (*   simpl; autounfold; simpl; *)
  (*     replace (1/2) with 0 by auto; try rewrite Zdiv_1_r; try rewrite Z.add_0_r; try rewrite Z.mul_0_r; try rewrite Zdiv_0_r. *)

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

  range_middle.
  destruct H8.
  split.
  apply (fun x => Z.le_trans _ _ _ x H8).
  easy.
  apply (Z.le_trans _ _ _ H9).
  easy.
  split.
  Definition
  Lemma 0 <= Z.pos p <= pmax -> (a + (two_power_pos p) / 2) / two_power_pos p
  (* assert(forall p, (Z.pos (shift_pos (Pos.succ p) 1) / 2) = (Z.pos (shift_pos p 1))). *)
  (* intro. unfold shift_pos. rewrite Pos.iter_succ. *)
  (* assert(forall p: positive, (Z.pos (xO p))/2 = Z.pos p). *)
  (* intro. rewrite Pos2Z.pos_xO. rewrite Z.mul_comm. apply Z.div_mul. omega. *)
  (* apply H8. *)
  (* rewrite H8. *)

  (* unfold Int.min_signed in *. simpl in *. unfold Z.shiftr, two_power_pos in *. simpl in *. *)


  split.
  repeat rewrite Int.Zshiftr_div_two_p.
  apply Zdiv_le_lower_bound.
  destruct q0.
  compute. trivial.
  compute. trivial.
  (* q0 is never negative *)
  assert (Hwrong : Z.neg p >= 0).
  easy.
  contradict Hwrong.
  easy.
  rewrite Z.mul_comm.

  apply Z.le_trans with (i0 * c0)%Z.

  (* evar (min_t: Z). *)
  (* evar (max_t: Z). *)
  (* assert (min_t <= i0 * c0 <= max_t); unfold min_t, max_t. *)
  (* eapply range_mul_rzero. *)

  range_right; try easy.

  rewrite Z.mul_comm. (* put two_p q0 on the right ot use range_mul_rzero *)



  (* match goal with *)
  (* | [ Hx: ?min_x <= i0 <= ?max_x, Hy: 0 <= c0 <= ?max_y |- _ ] => *)
  (*   apply (range_mul_rzero i0 c0 min_x max_x max_y); easy *)
  (* end. *)



    (* | ?x * ?y => *)
    (*   range x; range y; *)
    (*   match goal with *)
    (*   | [ Hx: ?min_x <= x <= ?max_x, Hy: ?min_y <= y <= ?max_y |- _ ] => *)




  (* Variable A: Set. *)
  (* Variable f: A -> A -> A. *)
  (* Infix "+" := f. *)
  (* Variable lt: A -> A -> Prop. *)
  (* Infix "<=" := lt. *)
  (* Inductive expr: Set := *)
  (* | Var: A -> expr *)
  (* | Add: expr -> expr -> expr. *)
  (* Fixpoint edenot (e: expr): A := *)
  (*   match e with *)
  (*   | Var v => v *)
  (*   | Add e1 e2 => edenot e1 + edenot e2 *)
  (*   end. *)
  (* Inductive range: Set := *)
  (* | Range: expr -> expr -> range. *)
  (* Fixpoint rdenot (r: range): Prop := *)
  (*   match r with *)
  (*   | Range e1 e2 =>  edenot e1 <= edenot e2 *)
  (*   end. *)
  (* Lemma combine_range: forall a b c: Z, x <= a -> y <= b <= y -> x + y <= a + b *)
  (* Fixpoint combine_range *)
  (* Fixpoint max_of (lr: list range) (e: expr) *)

  Lemma max_range_le: forall n: Z, n <= max_range n
  match goal with
  | [ |- ?a <= ?b + ?c ] =>
    destruct c
  end.
  destruct ((1 <<< q0) / two_p 1)).

  apply Z.le_trans with (i0 * c0)%Z.

  match goal with
  | [ Hx: ?low_x <= ?x <= ?hi_x, Hy: ?low_y <= ?y <= ?hi_y |- _ <= ?x * ?y ] =>
    let min_x := fresh "min_x" in
    remember (low_x * hi_y)%Z as min_x;
    apply Z.le_trans with min_x
    (* let v := constr:((low_x * 1)%Z) in *)
    (* pose v as min_x *)
    (* apply (Z.le_trans _ (low_x * low_y) _) *)
  end.




  Focus 2. (* Need le_add_pos_r like lt_add_pos _r *)

  contradict H2.
  rewrite Zlt_neg_0.
  apply Zdiv_le_upper_bound. compute. trivial.
  rewrite Z.mul_comm.

  rewrite Int.Zshiftl_mul_two_p.
  simpl.
  simpl
  unfold Z.shiftr. simpl.
  rewrite <- Z.add_0_r at 1.
  apply (Z.add_le_mono (Int.min_signed >>> 1) (i0*c0) 0 (1 <<< q0 >>> 1)).

  admit. (* od_mul_Z bounds *)

  forward.
  entailer!.
  forward.
  forward.
  remember (od_rotate_pi4_kernel_sub_avg_Z i0 i1 c0 q0 c1 q1) as res.
  Exists res.
  entailer!.
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
