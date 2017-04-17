Require Import progs.ghost.
Require Import mailbox.verif_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.kvnode.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(*Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.*)

Definition tnode := Tstruct _node noattr.

Opaque upto.

Definition make_loads lv := map (fun v => Load (vint v)) lv.

Definition read_spec :=
 DECLARE _read
 WITH n : val, out : val, sh : share, version : val, locs : list val,
   gv : val, hv : hist, ghosts : list val, hists : list hist
 PRE [ _n OF tptr tnode, _out OF tptr tint ]
  PROP (readable_share sh; Zlength ghosts = 8; Zlength hists = 8)
  LOCAL (temp _n n; temp _out out)
  SEP (data_at sh tnode (version, locs) n; data_at_ Tsh (tarray tint 8) out;
       atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv;
       fold_right sepcon emp (map (fun i => atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
         (fun _ _ => emp) (Znth i hists [])) (upto 8)))
 POST [ tvoid ]
  EX failvs : list Z, EX loops : Z, EX v : Z, EX hv' : hist, EX vals : list Z, EX hists' : list hist,
  PROP (Z.testbit v 0 = false; add_events hv (make_loads (failvs ++ [v; v])) hv'; Forall repable_signed failvs;
        Forall repable_signed vals; Zlength hists' = 8; loops <= Zlength failvs)
  LOCAL ()
  SEP (data_at sh tnode (version, locs) n; data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) out;
       atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv';
       fold_right sepcon emp (map (fun i => EX fails : list Z,
         !!(add_events (Znth i hists []) (make_loads (fails ++ [Znth i vals 0])) (Znth i hists' []) /\
            Zlength fails = loops) &&
         atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0 (fun _ _ => emp) (Znth i hists' []))
         (upto 8))).

Definition write_spec :=
 DECLARE _write
 WITH n : val, input : val, sh : share, version : val, locs : list val, vals : list Z,
   gv : val, hv : hist, ghosts : list val, hists : list hist
 PRE [ _n OF tptr tnode, _in OF tptr tint ]
  PROP (readable_share sh; Forall repable_signed vals; Zlength ghosts = 8; Zlength hists = 8)
  LOCAL (temp _n n; temp _in input)
  SEP (data_at sh tnode (version, locs) n; data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input;
       atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv;
       fold_right sepcon emp (map (fun i => atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
         (fun _ _ => emp) (Znth i hists [])) (upto 8)))
 POST [ tvoid ]
  EX v : Z, EX hv' : hist, EX hists' : list hist,
  PROP (add_events hv [Load (vint v); Store (vint (Z.lor v 1)); Store (vint (v + 2))] hv'; Zlength hists' = 8)
  LOCAL ()
  SEP (data_at sh tnode (version, locs) n; data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input;
       atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv';
       fold_right sepcon emp (map (fun i =>
       !!(add_events (Znth i hists []) [Store (vint (Znth i vals 0))] (Znth i hists' [])) &&
       atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0 (fun _ _ => emp) (Znth i hists' []))
       (upto 8))).

Definition Gprog : funspecs := ltac:(with_library prog [load_SC_spec; store_SC_spec; read_spec; write_spec]).

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.
(*Ltac entailer_for_return ::= go_lower; entailer'.*)

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_function.
  unfold atomic_loc_hist at 1; Intros.
  rewrite atomic_loc_isptr; Intros.
  forward.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call (AL_witness sh version gv 0 (fun _ _ => emp) hv emp (fun _ => emp)).
  { split; auto.
    apply AL_hist_spec; auto; repeat intro; auto. }
  Intros v; simpl; Intros hv1.
  forward_call (AS_witness sh version gv 0 (fun _ _ => emp) hv1 (Z.lor v 1) emp emp).
  { split; [|split; auto].
    apply AS_hist_spec; auto.
    repeat intro; auto.
    { apply derives_precise' with (Q := emp); auto; entailer!. }
    { admit. (* version stays in range *) } }
  Intros hv2.
  exploit (add_events_trans hv); eauto; intro.
  assert_PROP (Zlength vals = 8).
  { entailer!.
    rewrite Zlength_map in *; auto. }
  rewrite <- seq_assoc.
  forward_for_simple_bound 8 (EX i : Z, EX hists' : list hist, PROP (Zlength hists' = i)
    LOCAL (temp _v (vint v); temp _ver version; temp _n n; temp _in input)
    SEP (atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv2; @data_at CompSpecs sh tnode (version, locs) n;
         data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) input;
         fold_right sepcon emp (map (fun j =>
           !!(j < i -> add_events (Znth j hists []) [Store (vint (Znth j vals 0))] (Znth j hists' [])) &&
           atomic_loc_hist sh (Znth j locs Vundef) (Znth j ghosts Vundef) 0 (fun _ _ => emp)
             (if zlt j i then Znth j hists' [] else Znth j hists [])) (upto 8)))).
  { Exists (@nil hist); unfold atomic_loc_hist at 2; entailer!.
    apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    apply andp_right; [apply prop_right; omega|].
    destruct (zlt i 0); [omega | auto]. }
  - (* loop body *)
    rewrite extract_nth_sepcon with (i := i) by (rewrite Zlength_map; auto).
    erewrite Znth_map, Znth_upto by (auto; simpl; omega); Intros.
    destruct (zlt i i); [omega|].
    unfold atomic_loc_hist at 2; rewrite (atomic_loc_isptr _ (Znth i locs Vundef)); Intros.
    forward.
    forward.
    forward_call (AS_witness sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0 (fun _ _ => emp) (Znth i hists [])
      (Znth i vals 0) emp emp).
    { split; [|split; auto; apply Forall_Znth; auto; omega].
      apply AS_hist_spec; auto.
      repeat intro; auto.
      { apply derives_precise' with (Q := emp); auto; entailer!. } }
    Intros h'; Exists (x ++ [h']); rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
    intros.
    erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    destruct (eq_dec i (Zlength x)).
    + subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
      destruct (zlt (Zlength x) (Zlength x + 1)); [|omega].
      rewrite app_Znth2, Zminus_diag, Znth_0_cons by omega.
      apply andp_right; auto.
      apply prop_right; auto.
    + rewrite upd_Znth_diff' by (rewrite ?Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      Intros.
      destruct (zlt i (Zlength x)), (zlt i (Zlength x + 1)); try omega.
      * rewrite app_Znth1 by auto.
        apply andp_right; auto.
        apply prop_right; auto.
      * apply andp_right; auto.
        apply prop_right; omega.
  - Intros hists'.
    unfold atomic_loc_hist at 1; Intros.
    forward_call (AS_witness sh version gv 0 (fun _ _ => emp) hv2 (v + 2) emp emp).
    { split; [|split; auto].
      apply AS_hist_spec; auto.
      repeat intro; auto.
      { apply derives_precise' with (Q := emp); auto; entailer!. }
      { admit. (* version stays in range *) } }
    Intros hv3.
    forward.
    Exists v hv3 hists'; unfold atomic_loc_hist at 2; entailer!.
    + eapply add_events_trans with (le := [_; _]); eauto.
    + apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      Intros; destruct (zlt i 8); [|rewrite Zlength_upto in *; simpl in *; omega].
      apply andp_right; auto.
      apply prop_right; auto.
Admitted.

Lemma land_1 : forall i, Z.land i 1 = i mod 2.
Proof.
  intros; apply Z.land_ones with (n := 1); omega.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  apply semax_pre with (P' := EX failvs : list Z, EX loops : Z, EX hv' : hist, EX hists' : list hist,
    PROP (add_events hv (make_loads failvs) hv'; Forall repable_signed failvs; Zlength hists' = 8;
          loops <= Zlength failvs)
    LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ Tsh (tarray tint 8) out;
         atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv';
         fold_right sepcon emp (map (fun i => EX fails : list Z,
           !!(add_events (Znth i hists []) (make_loads fails) (Znth i hists' []) /\ Zlength fails = loops) &&
           atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0 (fun _ _ => emp) (Znth i hists' []))
           (upto 8)))).
  { Exists (@nil Z) 0 hv hists; entailer!.
    apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    Exists (@nil Z); entailer!. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  - Intros failvs loops hv' hists'.
    forward.
    unfold atomic_loc_hist at 1; rewrite atomic_loc_isptr; Intros.
    forward.
    assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
    forward_call (AL_witness sh version gv 0 (fun _ _ => emp) hv' emp (fun _ => emp)).
    { split; auto.
      apply AL_hist_spec; auto; repeat intro; auto. }
    Intros v; simpl; Intros hv1.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (Z.testbit v 0 = false) (LOCALx Q (SEPx R))) end.
    { eapply semax_pre; [|apply semax_continue].
      unfold POSTCONDITION, abbreviate, overridePost.
      destruct (eq_dec EK_continue EK_normal); [discriminate|].
      unfold loop1_ret_assert.
      Exists (failvs ++ [v]) loops hv1 hists'; entailer!.
      split; [unfold make_loads; rewrite map_app; eapply add_events_trans; eauto|].
      split; [rewrite Forall_app; auto|].
      rewrite Zlength_app, Zlength_cons, Zlength_nil; omega. }
    { forward.
      entailer!.
      unfold Int.one in *; rewrite and_repr, land_1, Zmod_odd in *.
      destruct (Z.odd v); auto; discriminate. }
    Intros.
    forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i; Forall repable_signed vals)
      LOCAL (temp _snap (vint v); temp _ver version; temp _n n; temp _out out)
      SEP (atomic_loc_hist sh version gv 0 (fun _ _ => emp) hv1; @data_at CompSpecs sh tnode (version, locs) n;
           data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals ++ repeat Vundef (Z.to_nat (8 - i))) out;
           EX hists'' : list hist, !!(Zlength hists'' = 8 /\ sublist i 8 hists'' = sublist i 8 hists') &&
           fold_right sepcon emp (map (fun j => EX fails : list Z, !!(add_events (Znth j hists [])
             (if zlt j i then make_loads (fails ++ [Znth j vals 0]) else make_loads fails) (Znth j hists'' []) /\
             Zlength fails = loops) &&
             atomic_loc_hist sh (Znth j locs Vundef) (Znth j ghosts Vundef) 0 (fun _ _ => emp)
               (Znth j hists'' [])) (upto 8)))).
    { Exists (@nil Z) hists'; unfold atomic_loc_hist at 2; rewrite data_at__eq; entailer!. }
    + (* loop body *)
      Intros hists''.
      rewrite extract_nth_sepcon with (i := i) by (rewrite Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; simpl; omega); Intros.
      destruct (zlt i i); [omega|].
      Intros fails.
      unfold atomic_loc_hist at 2; rewrite (atomic_loc_isptr _ (Znth i locs Vundef)); Intros.
      forward.
      forward_call (AL_witness sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0 (fun _ _ => emp)
        (Znth i hists'' []) emp (fun _ => emp)).
      { split; auto.
        apply AL_hist_spec; auto; repeat intro; auto. }
      Intros v'; simpl; Intros h'.
      forward.
      Exists (x ++ [v']) (upd_Znth i hists'' h').
      rewrite map_app.
      replace (8 - (i + 1)) with (8 - (Zlength (map (fun x => vint x) x ++ [vint v'])))
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_map; subst; auto).
      simpl map; rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      match goal with H : sublist _ _ hists'' = sublist _ _ hists' |- _ =>
        rewrite sublist_next with (i0 := i)(l := hists'')(d := []),
          sublist_next with (i0 := i)(l := hists')(d := []) in H by (auto; omega); inv H end.
      subst; rewrite Zlength_map, !Zlength_app, !Zlength_cons, !Zlength_nil; entailer!.
      { split; [rewrite Forall_app; auto|].
        rewrite upd_Znth_Zlength by omega; split; auto.
        rewrite sublist_upd_Znth_r by omega; auto. }
      rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map;
        auto; intros.
      erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      destruct (eq_dec i (Zlength x)).
      * subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto; omega).
        Exists fails.
        destruct (zlt (Zlength x) (Zlength x + 1)); [|omega].
        rewrite app_Znth2, Zminus_diag, Znth_0_cons by omega.
        entailer!.
        unfold make_loads; rewrite map_app; eapply add_events_trans; eauto.
      * rewrite !upd_Znth_diff' by (rewrite ?Zlength_map; auto; omega).
        erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
        Intros fails'; Exists fails'; entailer!.
        destruct (zlt i (Zlength x)), (zlt i (Zlength x + 1)); try omega; auto.
        rewrite app_Znth1; auto.
    + Intros vals hists''.
      unfold atomic_loc_hist at 1; Intros.
      forward_call (AL_witness sh version gv 0 (fun _ _ => emp) hv1 emp (fun _ => emp)).
      { split; auto.
        apply AL_hist_spec; auto; repeat intro; auto. }
      Intros v'; simpl; Intros hv2.
      match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (v' <> v) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists failvs loops v hv2 vals hists''; unfold atomic_loc_hist at 2; rewrite app_nil_r; entailer!.
        unfold make_loads; rewrite map_app; eapply add_events_trans; eauto.
        eapply add_events_trans with (le := [_]); eauto.
      * forward.
        entailer!.
      * intros; unfold overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        unfold POSTCONDITION, abbreviate, loop1_ret_assert.
        Intros; Exists (failvs ++ [v; v']) (loops + 1) hv2 hists''; unfold atomic_loc_hist at 2; entailer!.
        { rewrite Forall_app, Zlength_app, !Zlength_cons, Zlength_nil; repeat (constructor; auto); [|omega].
          unfold make_loads; rewrite map_app; eapply add_events_trans; eauto.
          eapply add_events_trans with (le := [_]); eauto. }
        apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
        erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
        Intros fails; Exists (fails ++ [Znth i vals 0]); entailer!.
        destruct (zlt i 8); [|rewrite Zlength_upto in *; simpl in *; omega].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; split; auto.
Qed.