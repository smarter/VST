Require Import VST.floyd.proofauto.
Require Import wand_demo.bst.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.

Section TREES.
Variable V : Type.
Variable default: V.

Definition key := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else pushdown_left a b
 end.

End TREES.
Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Fixpoint tree_rep (t: tree val) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.

Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.

(* TODO: seems not useful *)
Lemma treebox_rep_spec: forall (t: tree val) (b: val),
  treebox_rep t b =
  EX p: val, 
  match t with
  | E => !!(p=nullval) && data_at Tsh (tptr t_struct_tree) p b
  | T l x v r => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      data_at Tsh (tptr t_struct_tree) p b *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      field_at Tsh t_struct_tree [StructField _value] v p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  unfold treebox_rep at 1.
  f_equal.
  extensionality p.
  destruct t; simpl.
  + apply pred_ext; entailer!.
  + unfold treebox_rep.
    apply pred_ext; entailer!.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at 1%nat.
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at 3%nat.
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
Qed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (memory_block Tsh n v).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().

Definition insert_spec :=
 DECLARE _insert
  WITH p0: val, x: Z, v: val, t0: tree val
  PRE  [ _p OF (tptr (tptr t_struct_tree)), _x OF tint,
        _value OF (tptr Tvoid)   ]
    PROP( Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    LOCAL(temp _p p0; temp _x (Vint (Int.repr x)); temp _value v)
    SEP (treebox_rep t0 p0)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (insert x v t0) p0).

Definition lookup_spec :=
 DECLARE _lookup
  WITH p0: val, x: Z, v: val, t0: tree val
  PRE  [ _p OF (tptr (tptr t_struct_tree)), _x OF tint  ]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _p p0; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t0 p0)
  POST [ tptr Tvoid ]
    PROP()
    LOCAL(temp ret_temp (lookup nullval x t0))
    SEP (treebox_rep t0 p0).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: tree val, x: Z, vx: val, tb: tree val, y: Z, vy: val, tc: tree val, b: val, l: val, pa: val, r: val
  PRE  [ __l OF (tptr (tptr (Tstruct _tree noattr))),
        _l OF (tptr (Tstruct _tree noattr)),
        _r OF (tptr (Tstruct _tree noattr))]
    PROP(Int.min_signed <= x <= Int.max_signed; is_pointer_or_null vx)
    LOCAL(temp __l b; temp _l l; temp _r r)
    SEP (data_at Tsh (tptr t_struct_tree) l b;
         data_at Tsh t_struct_tree (Vint (Int.repr x), (vx, (pa, r))) l;
         tree_rep ta pa;
         tree_rep (T tb y vy tc) r)
  POST [ Tvoid ] 
    EX pc: val,
    PROP(Int.min_signed <= y <= Int.max_signed; is_pointer_or_null vy)
    LOCAL()
    SEP (data_at Tsh (tptr t_struct_tree) r b;
         data_at Tsh t_struct_tree (Vint (Int.repr y), (vy, (l, pc))) r;
         tree_rep (T ta x vx tb) l;
         tree_rep tc pc).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: tree val, x: Z, v: val, tb: tree val, b: val, p: val
  PRE  [ _t OF (tptr (tptr (Tstruct _tree noattr)))]
    PROP(Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) v)
    LOCAL(temp _t b)
    SEP (data_at Tsh (tptr t_struct_tree) p b;
         field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p;
         field_at Tsh t_struct_tree [StructField _value] v p;
         treebox_rep ta (field_address t_struct_tree [StructField _left] p);
         treebox_rep tb (field_address t_struct_tree [StructField _right] p))
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (pushdown_left ta tb) b).

Definition delete_spec :=
 DECLARE _delete
  WITH b: val, x: Z, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (delete x t) b).

Definition Gprog : funspecs :=
    ltac:(with_library prog [
    mallocN_spec; freeN_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec
  ]).

Lemma tree_rep_saturate_local:
   forall t p, tree_rep t p |-- !! is_pointer_or_null p.
Proof.
destruct t; simpl; intros.
entailer!.
Intros pa pb. entailer!.
Qed.

Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.

Lemma ramify_PPQQ {A: Type} {NA: NatDed A} {SA: SepLog A} {CA: ClassicalSep A}: forall P Q,
  P |-- P * (Q -* Q).
Proof.
  intros.
  apply RAMIF_PLAIN.solve with emp.
  + rewrite sepcon_emp; auto.
  + rewrite emp_sepcon; auto.
Qed.

Lemma tree_rep_nullval: forall t,
  tree_rep t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl tree_rep.
  Intros pa pb. entailer!.
Qed.

Hint Resolve tree_rep_nullval: saturate_local.

Lemma is_pointer_or_null_force_val_sem_cast_neutral: forall p,
  is_pointer_or_null p -> force_val (sem_cast_neutral p) = p.
Proof.
  intros.
  destruct p; try contradiction; reflexivity.
Qed.

Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.

Lemma bst_left_entail: forall (t1 t1' t2: tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
       (treebox_rep t1'
         (field_address t_struct_tree [StructField _left] p) -*
        treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  cancel.
Qed.

Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, P |-- Q -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; omega)
                          | rewrite if_falseb by (apply Z.ltb_ge; omega)].

Definition insert_inv (p0: val) (t0: tree val) (x: Z) (v: val): environ -> mpred :=
  EX p: val, EX t: tree val,
  PROP()
  LOCAL(temp _p p; temp _x (Vint (Int.repr x));   temp _value v)
  SEP(treebox_rep t p;  (treebox_rep (insert x v t) p -* treebox_rep (insert x v t0) p0)).

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ (insert_inv p0 t0 x v) (insert_inv p0 t0 x v) )].
  * (* Precondition *)
    unfold insert_inv.
    Exists p0 t0. entailer.
    apply ramify_PPQQ.
  * (* Loop body *)
    unfold insert_inv.
    Intros p t.
    forward. (* Sskip *)
    unfold treebox_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; repable_signed.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. simpl tree_rep. rewrite !prop_true_andp by auto.
      rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      apply modus_ponens_wand'.
      apply treebox_rep_leaf; auto.
    + (* else clause *)
      destruct t.
        { simpl tree_rep. normalize. }
      simpl tree_rep.
      Intros qa qb. clear H1.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        unfold insert_inv.
        Exists (offset_val 8 q) t1.
        entailer!.
        simpl_compb.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 8 q)
          with (field_address t_struct_tree [StructField _left] q)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_left_entail; auto.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        unfold insert_inv.
        Exists (offset_val 12 q) t2.
        entailer!.
        simpl_compb; simpl_compb.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 12 q)
          with (field_address t_struct_tree [StructField _right] q)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_right_entail; auto.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H1 H4.
        forward. (* q->value=value *)
        forward. (* return *)
        (* TODO: SIMPLY THIS LINE *)
        simpl_compb.
        simpl_compb.
        apply modus_ponens_wand'.
        unfold treebox_rep. Exists q.
        simpl tree_rep. Exists qa qb. entailer!.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.

Definition lookup_inv (q0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX q: val, EX t: tree val, 
  PROP(lookup nullval x t = lookup nullval x t0) 
  LOCAL(temp _q q; temp _x (Vint (Int.repr x)))
  SEP(tree_rep t q;  (tree_rep t q -* tree_rep t0 q0)).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold treebox_rep. Intros q0.
  forward. (* q=*p; *)
  apply (semax_post_ret1 nil
          (data_at Tsh (tptr t_struct_tree) q0 p0 :: tree_rep t0 q0 :: nil)).
  1: intro HH; inversion HH.
  1: unfold treebox_rep; Exists q0; entailer!.
  apply semax_frame''.
  forward_while (lookup_inv q0 t0 x).
  * (* precondition implies loop invariant *)
    Exists q0 t0. entailer!.
    apply -> wand_sepcon_adjoint. cancel.
  * (* type-check loop condition *)
    entailer!.
  * (* loop body preserves invariant *)
    destruct t; unfold tree_rep at 1; fold tree_rep. normalize.
    Intros qa qb.
    forward.
    forward_if; [ | forward_if ].
    + (* then clause: x<y *)
      forward. (* q=q<-left *)
      Exists (qa,t1). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        Exists qa qb; entailer!.
    + (* else-then clause: y<x *)
      forward. (* q=q<-right *)
      Exists (qb,t2). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        Exists qa qb; entailer!.
    + (* else-else clause: x=y *)
      assert (x=k) by omega. subst x. clear H H4 H5.
      forward. (* v=q->value *)
      forward. (* return v; *)
      unfold treebox_rep. unfold normal_ret_assert.
      entailer!.
      - rewrite <- H0. simpl.
        simpl_compb; simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply modus_ponens_wand'.
        Exists qa qb; entailer!.
  * (* after the loop *)
    forward. (* return NULL; *)
    entailer!.
    apply modus_ponens_wand.
Qed.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  simpl.
  Intros pb pc.
  forward. (* mid=r->left *)
  forward. (* l->right=mid *)
  assert_PROP (is_pointer_or_null pb) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* r->left=l *)
  assert_PROP (is_pointer_or_null l) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* _l = r *)
  assert_PROP (is_pointer_or_null r) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  Opaque tree_rep. forward. Transparent tree_rep. (* return *)
  (* TODO: simplify the following proof *)
  Exists pc.
  entailer!.
  simpl.
  Exists pa pb.
  entailer!.
Qed.

Definition pushdown_left_inv (b_res: val) (t_res: tree val): environ -> mpred :=
  EX b: val, EX ta: tree val, EX x: Z, EX v: val, EX tb: tree val,
  PROP  () 
  LOCAL (temp _t b)
  SEP   (treebox_rep (T ta x v tb) b;
         (treebox_rep (pushdown_left ta tb) b -* treebox_rep t_res b_res)).

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ (pushdown_left_inv b (pushdown_left ta tb))
                         (pushdown_left_inv b (pushdown_left ta tb)))].
  + (* Precondition *)
    unfold pushdown_left_inv.
    Exists b ta x v tb.
    entailer!.
    eapply derives_trans; [| apply ramify_PPQQ].
    rewrite (treebox_rep_spec (T ta x v tb)).
    Exists p.
    entailer!.
  + (* Loop body *)
    unfold pushdown_left_inv.
    clear x v H H0.
    Intros b0 ta0 x vx tbc0.
    unfold treebox_rep at 1.
    Intros p0.
    forward. (* skip *)
    forward. (* p = *t; *)
      (* TODO entailer: The following should be solve automatically. satuate local does not work *)
      1: rewrite (add_andp _ _ (tree_rep_saturate_local _ _)); entailer!.
    simpl tree_rep.
    Intros pa pbc.
    forward. (* q = p->right *)
    forward_if.
    - subst.
      assert_PROP (tbc0 = (@E _)).
        1: entailer!.
      subst.
      forward. (* q=p->left *)
      forward. (* *t=q *)
      forward_call (p0, sizeof t_struct_tree). (* freeN(p, sizeof ( *p )); *)
      Focus 1. {
        entailer!.
        rewrite memory_block_data_at_ by auto.
        cancel.
      } Unfocus.
      forward. (* return *)
      apply modus_ponens_wand'.
      Exists pa.
      cancel.
    - destruct tbc0 as [| tb0 y vy tc0].
        { simpl tree_rep. normalize. }
      forward_call (ta0, x, vx, tb0, y, vy, tc0, b0, p0, pa, pbc). (* turn_left(t, p, q); *)
      Intros pc.
      forward. (* t = &q->left; *)
      Exists (field_address t_struct_tree [StructField _left] pbc) ta0 x vx tb0.
      (* TODO entailer: not to simply too much in entailer? *)
      Opaque tree_rep. entailer!. Transparent tree_rep.
        (* TODO: simplify this line *)
      apply RAMIF_PLAIN.trans'.
      apply bst_left_entail; auto.
  + forward. (* Sskip *)
    auto.
Qed.

Definition delete_inv (b0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX b: val, EX t: tree val,
  PROP()
  LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
  SEP(treebox_rep t b;  (treebox_rep (delete x t) b -* treebox_rep (delete x t0) b0)).

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ (delete_inv b t x) (delete_inv b t x) )].
  * (* Precondition *)
    unfold delete_inv.
    Exists b t. entailer.
    apply ramify_PPQQ.
  * (* Loop body *)
    unfold delete_inv.
    Intros b1 t1.
    forward. (* Sskip *)
    unfold treebox_rep at 1. Intros p1.
    forward. (* p = *t; *)
    forward_if.
    + (* then clause *)
      subst p1.
      assert_PROP (t1= (@E _)).
        1: entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp by auto.
      forward. (* return; *)
      unfold treebox_rep at 1.
      apply modus_ponens_wand'.
      Exists nullval.
      simpl tree_rep.
      entailer!.
    + (* else clause *)
      destruct t1.
        { simpl tree_rep. normalize. }
      simpl tree_rep.
      Intros pa pb. clear H0.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold delete_inv.
        Exists (offset_val 8 p1) t1_1.
        entailer!.
        simpl_compb.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 8 p1)
          with (field_address t_struct_tree [StructField _left] p1)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_left_entail; auto.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold delete_inv.
        Exists (offset_val 12 p1) t1_2.
        entailer!.
        simpl_compb; simpl_compb.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 12 p1)
          with (field_address t_struct_tree [StructField _right] p1)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_right_entail; auto.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x.
        unfold_data_at 2%nat.
        gather_SEP 3 5.
        replace_SEP 0 (treebox_rep t1_1 (field_address t_struct_tree [StructField _left] p1)).
        Focus 1. {
          unfold treebox_rep; entailer!.
          Exists pa.
          rewrite field_at_data_at.
          entailer!.
        } Unfocus.
        gather_SEP 4 5.
        replace_SEP 0 (treebox_rep t1_2 (field_address t_struct_tree [StructField _right] p1)).
        Focus 1. {
          unfold treebox_rep; entailer!.
          Exists pb.
          rewrite field_at_data_at.
          entailer!.
        } Unfocus.
        forward_call (t1_1, k, v, t1_2, b1, p1).
        forward. (* return *)
        simpl_compb.
        simpl_compb.
        apply modus_ponens_wand'.
        auto.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.
