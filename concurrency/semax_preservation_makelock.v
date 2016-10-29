Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.juicy_safety.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import floyd.coqlib3.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.coqlib5.
Require Import concurrency.permjoin.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.
Require Import concurrency.age_to.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.sync_preds.
Require Import concurrency.join_lemmas.
Require Import concurrency.aging_lemmas.
Require Import concurrency.cl_step_lemmas.
Require Import concurrency.resource_decay_lemmas.
Require Import concurrency.resource_decay_join.
Require Import concurrency.semax_invariant.
Require Import concurrency.semax_simlemmas.
Require Import concurrency.sync_preds.
Require Import concurrency.lksize.
Require Import concurrency.rmap_locking.

Local Arguments getThreadR : clear implicits.
Local Arguments getThreadC : clear implicits.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread : clear implicits.
Local Arguments updThreadR : clear implicits.
Local Arguments updThreadC : clear implicits.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Lemma matchfunspec_common_join e Gamma phi phi' psi Phi Phi' :
  join phi psi Phi ->
  join phi' psi Phi' ->
  matchfunspec e Gamma Phi ->
  matchfunspec e Gamma Phi'.
Proof.
  intros j j' M b fs.
  specialize (M b fs).
Admitted.

Lemma preservation_makelock
  (lockSet_Writable_updLockSet_updThread
     : forall (m m' : Memory.mem) (i : tid) (tp : thread_pool) (Phi : LocksAndResources.res),
       mem_compatible_with tp m Phi ->
       forall (cnti : containsThread tp i) (b : block) (ofs : int) (ophi : option rmap)
         (ophi' : LocksAndResources.lock_info) (c' : ctl) (phi' : LocksAndResources.res) 
         (z : int) (pr : mem_compatible tp m),
       AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi ->
       Mem.store Mint32 (restrPermMap (mem_compatible_locks_ltwritable pr)) b (Int.intval ofs) (Vint z) = Some m' ->
       lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Int.intval ofs) ophi')) m') 
  (mem_cohere'_store : forall m tp m' b ofs i Phi
    (Hcmpt : mem_compatible tp m),
    lockRes tp (b, Int.intval ofs) <> None ->
    Mem.store
      Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcmpt))
      b (Int.intval ofs) (Vint i) = Some m' ->
    mem_compatible_with tp m Phi (* redundant with Hcmpt, but easier *) ->
    mem_cohere' m' Phi)
  (personal_mem_equiv_spec
     : forall (m m' : Mem.mem') (phi : rmap) (pr : mem_cohere' m phi) (pr' : mem_cohere' m' phi),
       Mem.nextblock m = Mem.nextblock m' ->
       (forall loc : address, max_access_at m loc = max_access_at m' loc) ->
       (forall loc : AV.address, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
       mem_equiv (m_dry (personal_mem m phi pr)) (m_dry (personal_mem m' phi pr')))
  (CS : compspecs)
  (ext_link : string -> ident)
  (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
  (Jspec' := @OK_spec (Concurrent_Espec unit CS ext_link))
  (Jspec'_juicy_mem_equiv : Jspec'_juicy_mem_equiv_def CS ext_link)
  (Jspec'_hered : Jspec'_hered_def CS ext_link)
  (Gamma : PTree.t funspec)
  (n : nat)
  (ge : SEM.G)
  (m m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp tp' : thread_pool)
  (INV : state_invariant Jspec' Gamma (S n) (m, ge, (i :: sch, tp)))
  (Phi : rmap)
  (compat : mem_compatible_with tp m Phi)
  (lev : level Phi = S n)
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (sparse : lock_sparsity (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : threads_safety Jspec' m ge tp Phi compat (S n))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei cnti : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (ci : code)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (ev : Events.sync_event)
  (Hcmpt : mem_compatible tp m)
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (Htstep : syncStep ge Htid Hcmpt tp' m' ev)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m')
  (tp_ := tp' : thread_pool)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (tp'0 tp'' : thread_pool)
  (jm : juicy_mem)
  (c : code)
  (b : block)
  (ofs : int)
  (R : pred rmap)
  (phi' : rmap)
  (m'0 : Memory.mem)
  (Hcompatible : mem_compatible tp m)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (MKLOCK, Vptr b ofs :: nil))
  (* (Hright_juice : m = m_dry jm) *)
  (Hpersonal_perm : personal_mem m (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid) = jm)
  (Hpersonal_juice : getThreadR i tp Htid = m_phi jm)
  (Hstore : Mem.store Mint32 (m_dry jm) b (Int.intval ofs) (Vint Int.zero) = Some m')
  (Hrmap : rmap_makelock (getThreadR i tp cnti) phi' (b, Int.unsigned ofs) R LKSIZE)
  (Htp' : tp'0 = updThread i tp Htid (Kresume c Vundef) phi')
  (Htp'' : tp' = age_tp_to (level (m_phi jm) - 1) (updLockSet tp'0 (b, Int.intval ofs) None))
  (H : tp'' = tp')
  (H0 : m'0 = m')
  (H1 : Events.mklock (b, Int.intval ofs) = ev) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).

Proof.
  clear lockSet_Writable_updLockSet_updThread.
  clear mem_cohere'_store.
  clear personal_mem_equiv_spec.
  assert (Hpos : (0 < LKSIZE)%Z) by reflexivity.
  assert (j : join_sub (getThreadR i tp cnti) Phi) by apply compatible_threadRes_sub, compat.
  destruct j as (psi & jphi).
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos Hrmap jphi as RL.
  destruct RL as (Phi' & Hrmap' & jphi').
  
  assert (cnti = Htid) by apply proof_irr; subst Htid.
  
  assert (LPhi' : level Phi' = level Phi) by (destruct Hrmap'; auto).
  
  assert (notfound : lockRes tp (b, Int.intval ofs) = None). {
    spec lock_coh (b, Int.intval ofs). cleanup.
    destruct (AMap.find _ _) as [o|] eqn:Eo. 2:reflexivity. exfalso.
    assert (C : exists (sh : Share.t) (R : pred rmap), (sync_preds_defs.LK_at R sh (b, Int.intval ofs)) Phi).
    destruct o; breakhyps; eauto. clear lock_coh.
    destruct C as (sh & R' & At).
    destruct Hrmap' as (_ & _ & inside).
    spec inside (b, Int.intval ofs).
    spec inside. split; auto; unfold Int.unsigned in *; lkomega.
    destruct inside as (val' & sh'' & E & _).
    spec At (b, Int.intval ofs). simpl in At.
    if_tac in At. 2:range_tac.
    if_tac in At. 2:tauto.
    breakhyps.
  }
  
  assert (APhi' : age Phi' (age_to n Phi')) by (apply age_to_1; congruence).
        
  assert (Phi'rev : forall sh psh k pp' loc,
             ~adr_range (b, Int.unsigned ofs) LKSIZE loc ->
             age_to n Phi' @ loc = YES sh psh k pp' ->
             exists pp,
               Phi @ loc = YES sh psh k pp /\
               pp' = preds_fmap (approx n) (approx n) pp).
  {
    destruct Hrmap.
    intros sh psh k pp' loc nr E''.
    destruct Hrmap' as (_ & E & _).
    rewrite E; eauto.
    rewrite (age_resource_at APhi' (loc := loc)) in E''.
    destruct (Phi' @ loc); simpl in E''; try congruence.
    injection E''; intros <- <- <- <- ; eexists; split. reflexivity.
    rewrite level_age_to. 2:omega. reflexivity.
  }
  
  assert (mcompat' : mem_compatible_with' tp_ m_ (age_to n Phi')). {
    subst m_ tp_ m'0 tp'' tp'0 tp'.
    constructor.
    + (* join_all *)
      rewrite <-Hpersonal_juice. autospec El. cleanup. rewrite El.
      apply join_all_age_to. cleanup. omega.
      pose proof juice_join compat as j.
      rewrite join_all_joinlist.
      rewrite join_all_joinlist in j.
      rewrite maps_updlock1.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      rewrite maps_getlock1. 2:assumption.
      rewrite maps_getthread with (cnti := cnti) in j.
      destruct j as (psi_ & jpsi_ & jphi_).
      exists psi; split. 2:assumption.
      cut (psi = psi_). now intros <-; auto.
      eapply join_canc. eapply join_comm. apply jphi. eapply join_comm. eauto.
    
    + (* mem_cohere' *)
      split.
      * intros rsh sh v loc pp E''.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- exfalso.
           destruct Hrmap' as (_ & _ & inside). spec inside loc. autospec inside.
           rewrite age_to_resource_at in E''.
           destruct inside as (? & ? & _ & E').
           rewrite E' in E''. if_tac in E''; simpl in E''; congruence.
        -- destruct (Phi'rev _ _ _ _ _ nr E'') as (pp' & E & ->).
           cut (contents_at m loc = v /\ pp' = NoneP).
           { intros []; split; subst pp'; auto.
             destruct loc as (b1, ofs1).
             destruct (store_outside' _ _ _ _ _ _ Hstore) as (outside & _ & _).
             spec outside b1 ofs1.
             destruct outside as [(->, r) | same].
             - exfalso. apply nr. split; auto.
             - rewrite <-same.
               subst jm. unfold personal_mem.
               change (m_dry (mkJuicyMem ?m _ _ _ _ _)) with m.
               rewrite <-juicyRestrictContents. auto.
           }
           eapply (cont_coh (all_cohere compat)); eauto.
      
      * (* access_cohere' *)
        intros loc.
        admit (* wait for change in access_cohere' from nick and santiago *).
      
      * (* max_access_cohere *)
        intros loc.
        admit (* implied by above -- or the opposite *).
      
      * (* alloc_cohere *)
        pose proof all_coh ((all_cohere compat)) as A.
        unfold alloc_cohere in *.
        destruct (store_outside' _ _ _ _ _ _ Hstore) as (_ & _ & <-).
        subst jm; simpl.
        intros loc out.
        destruct Hrmap' as (_ & outside & inside).
        spec outside loc.
        spec outside.
        { destruct loc as (b', ofs').
          intros [<- _].
          spec A (b, Int.intval ofs) out.
          spec inside (b, Int.unsigned ofs).
          spec inside. split; auto. lkomega.
          unfold Int.unsigned in *.
          if_tac in inside;
          breakhyps. }
        spec A loc out.
        rewrite age_to_resource_at, <-outside, A.
        reflexivity.
    
    + (* lockSet_Writable *)
      apply lockSet_Writable_age.
      intros b' ofs'.
      unfold lockGuts in *.
      simpl.
      rewrite AMap_find_add.
      intros H ofs0 H0.
      rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
      revert H ofs0 H0.
      intros H ofs0 H0.
      subst jm.
      unfold personal_mem.
      change (m_dry (mkJuicyMem ?m _ _ _ _ _)) with m.
      pose proof juicyRestrictMax as RR.
      specialize RR _ _ _ (b', ofs0).
      unfold max_access_at in *.
      unfold access_at in *.
      simpl fst in RR. simpl snd in RR.
      rewrite <-RR. clear RR.
      revert H ofs0 H0.
      if_tac [e | ne].
      * injection e as <- <-.
        intros _ ofs0 r.
        pose proof all_cohere compat as C. destruct C as [_ _ C _].
        destruct Hrmap' as (_ & _ & inside).
        specialize (inside (b, ofs0)).
        spec C (b, ofs0).
        spec inside. hnf. split; auto.
        destruct inside as (val & sh & E & _).
        rewrite E in C.
        unfold max_access_at in *.
        eapply po_trans. eassumption.
        unfold perm_of_sh in *.
        Ltac share_tac :=
          change (pshare_sh pfullshare) with Share.top in *;
          pose proof Share.nontrivial;
          try tauto.
        repeat if_tac; try constructor; share_tac.
      * eapply loc_writable; eauto.
    
    + (* juicyLocks_in_lockSet *)
      intros loc sh psh P z E''.
      unfold lockGuts in *.
      rewrite lset_age_tp_to.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_add. if_tac [<- | ne]. reflexivity.
      destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' E'') as (pp, E').
      cut (Phi @ loc = YES sh psh (LK z) pp).
      { intros; eapply (jloc_in_set compat); eauto. }
      rewrite <-E'.
      destruct Hrmap' as (_ & outside & inside).
      apply outside.
      intros r.
      spec inside loc r.
      destruct inside as (val & sh' & _ & E1).
      rewrite E1 in E'.
      if_tac in E'.
      * unfold Int.unsigned in *. congruence.
      * congruence.
    
    + (* lockSet_in_juicyLocks *)
      (* mindless *)
      admit.
  }
  
  subst m_ tp_ m'0 tp'' tp'0 tp'.
  unshelve eapply state_invariant_c with (PHI := age_to n Phi') (mcompat := mcompat').
  - (* level *)
    apply level_age_to. omega.
  
  - (* matchfunspec *)
    apply matchfunspec_age_to.
    eapply matchfunspec_common_join with (Phi := Phi); eauto.
  
  - (* lock sparsity *)
    simpl.
    cleanup.
    unfold lock_sparsity in *.
    cut (forall loc, AMap.find loc (lset tp) <> None ->
                loc = (b, Int.intval ofs) \/ fst loc <> b \/ fst loc = b /\ far (snd loc) (Int.intval ofs)). {
      clear -sparse.
      intros H loc1 loc2.
      do 2 rewrite AMap_find_map_option_map. cleanup.
      do 2 rewrite AMap_find_add.
      if_tac [<- | ne1]; if_tac [<- | ne2]; simpl.
      - auto.
      - intros _ found2.
        spec H loc2. spec H. destruct (AMap.find loc2 _); auto; congruence.
        breakhyps. right. right. split; auto. unfold far in *; auto. zify. omega.
      - intros found1 _.
        spec H loc1. spec H. destruct (AMap.find loc1 _); auto; congruence.
        auto.
      - intros found1 found2.
        spec sparse loc1 loc2.
        spec sparse. destruct (AMap.find loc1 _); auto; congruence.
        spec sparse. destruct (AMap.find loc2 _); auto; congruence.
        auto.
    }
    clear sparse jmstep Htstep.
    intros loc found. right.
    specialize (lock_coh loc). destruct (AMap.find loc _) as [o|] eqn:Eo. clear found. 2:congruence.
    assert (coh : exists (sh : Share.t) (R : pred rmap), (sync_preds_defs.LK_at R sh loc) Phi)
      by (destruct o; breakhyps; eauto). clear lock_coh.
    destruct coh as (sh & R' & AT).
    specialize (AT loc).
    destruct Hrmap.
    admit (* mindless *).
  
  - (* lock coherence *)
    unfold lock_coherence'.
    (* Have we not proved that before? Not exactly: lock_coherence
    talks about the dry memory, which is defined as the restrPermMap
    of something that uses mem_compatible, which in turn uses the lock
    coherence above *)
    simpl.
    intros loc.
    rewrite AMap_find_map_option_map.
    rewrite AMap_find_add.
    if_tac.
    + split.
      * (* load_at *)
        admit (* should be fine *).
      * (* LK_at *)
        unfold sync_preds_defs.LK_at in *.
        unfold sync_preds_defs.LKspec_ext in *.
        (* we do NOT have LK_at. we have only "at least" something, but again not a rectangle. *)
        admit.
    + spec lock_coh loc.
      destruct (AMap.find loc _) as [o|] eqn:Eo.
      * destruct o; unfold option_map; destruct lock_coh as (load & coh); split; swap 2 3.
        -- admit. (* load *)
        -- admit. (* load *)
        -- admit. (* lkat *)
        -- admit. (* lkat *)
      * unfold option_map.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- destruct Hrmap' as (_ & _ & inside).
           spec inside loc r. rewrite isLK_age_to.
           if_tac in inside; intros []; intros ? ?; breakhyps.
        -- destruct Hrmap' as (_ & outside & _).
           rewrite age_to_resource_at.
           spec outside loc nr. rewrite <-outside.
           clear -lock_coh.
           unfold isLK, isCT in *.
           destruct (Phi @ loc) as [t0 | t0 p [] p0 | k p]; (* split; *) simpl in *; intro; breakhyps.
           apply lock_coh; eauto.
  
  - (* thread safety *)
    admit.
  
  - (* well_formedness *)
    intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gLockSetCode; auto.
    destruct (eq_dec i j).
    * subst j.
      rewrite gssThreadCode.
      replace lj with cnti in wellformed by apply proof_irr.
      rewrite Hthread in wellformed.
      auto.
    * unshelve erewrite gsoThreadCode; auto.
         
  - (* uniqueness *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti).
    rewrite Hthread.
    congruence.
Admitted.

    (* now much easier with rmap_makelock.
    (* we must define the new Phi *)
    
    Definition rmap_makelock phi phi' sh loc R :=
      (forall x, ~ adr_range loc LKSIZE x -> phi @ x = phi' @ x) /\
      (forall x, adr_range loc LKSIZE x -> exists val, phi @ x = YES sh pfullshare (VAL val) NoneP) /\
      (LKspec_ext R fullshare fullshare loc phi').
    Definition rmap_freelock phi phi' sh loc R :=
      (forall x, ~ adr_range loc LKSIZE x -> phi @ x = phi' @ x) /\
      (LKspec_ext R fullshare fullshare loc phi) /\
      (forall x, adr_range loc LKSIZE x -> exists val, phi' @ x = YES sh pfullshare (VAL val) NoneP).
    
    assert (HPhi' : exists Phi', rmap_makelock Phi Phi' sh (b, Int.intval ofs) R). {
(*      pose (f' :=
              fun loc =>
                if adr_range_dec (b, Int.intval ofs) LKSIZE loc then
                  if eq_dec (Int.intval ofs) (snd loc) then
                    LK  *)
      admit.
    }
    destruct HPhi' as (Phi' & HPhi').
    
    subst m_ tp' tp'0 m'0.
    pose (tp2 := (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None)).
    fold tp2 in H.
    assert (compat' : mem_compatible_with tp2 m' Phi'). {
      unfold tp2.
      (*
      below, without the modification of the Phi'
      rewrite <-Hpersonal_juice.
      rewrite El.
      constructor.
      - (* joining to global map: the acquired rmap move from
            lockset to threads's maps *)
        pose proof juice_join compat as J.
        apply join_all_age_to. cleanup. omega.
        rewrite join_all_joinlist in J |- *.
        rewrite maps_updlock1.
        rewrite maps_remLockSet_updThread.
        rewrite maps_updthread.
        erewrite (maps_getthread i _ Htid) in J; eauto.
        clear -J Hct0 Hct Hj_forward Hpersonal_juice lock_coh levphi' Hlock.
        rewrite maps_getlock1; swap 1 2. {
          specialize (lock_coh (b, Int.intval ofs)).
          cleanup.
          destruct (AMap.find _ _) as [o|]; auto. exfalso.
          specialize (Hct (Int.intval ofs)).
          assert_specialize Hct. split. omega. unfold LKSIZE; simpl. omega.
          destruct Hct as (val & sh'' & E).
          assert (j : join_sub (getThreadR i tp Htid) Phi) by apply compatible_threadRes_sub, compat.
          destruct j as (?, j).
          apply resource_at_join with (loc := (b, Int.intval ofs)) in j.
          rewrite Hpersonal_juice in j.
          rewrite E in j.
          destruct o.
          - destruct lock_coh as (_ & sh' & R' & lk & _).
            apply predat2 in lk.
            unfold predat in *.
            inv j; breakhyps.
          - destruct lock_coh as (_ & sh' & R' & lk).
            apply predat2 in lk.
            unfold predat in *.
            inv j; breakhyps.
        }
        destruct J as (psi & j1 & j2).
        exists psi; split; auto.
        apply resource_at_join2.
        + rewrite levphi'. rewrite <-Hpersonal_juice. join_level_tac.
        + join_level_tac.
        + intros (b', ofs').
          rewrite Hpersonal_juice in j2.
          apply resource_at_join with (loc := (b', ofs')) in j2.
          specialize (Hj_forward (b', ofs')). simpl in Hj_forward.
          destruct (adr_range_dec (b, Int.intval ofs) 4 (b', ofs')) as [a|a]; swap 1 2.
          * assert_specialize Hj_forward. 2:congruence.
            unfold adr_range in *.
            unfold LKSIZE in *.
            simpl. cut ( b <> b' \/ ~ (Int.intval ofs <= ofs' < Int.intval ofs + 4)%Z). admit. (* wtf machine *)
            tauto.
          * unfold adr_range in *.
            destruct a as [<- a].
            specialize (Hct ofs'). autospec Hct.
            destruct Hct as (val & sh' & E).
            rewrite E in j2.
            destruct (eq_dec ofs' (Int.intval ofs)) as [e|e].
            -- subst ofs'.
               rewrite Hlock.
               inv j2.
               ++ (* NOT THE SAME PHI *)
                 admit.
       *) *)