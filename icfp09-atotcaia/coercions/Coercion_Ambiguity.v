Require Export Coercion_WF_Coerciongen.
Set Undo 100000.

Hint Constructors coercion.
Hint Unfold coerciongen.
Hint Resolve in_eq in_cons in_inv in_nil insingleton.
Hint Resolve coercion_pi_strengthening.
Require Import Classical.
Hint Resolve altnosub_to_altsub.

Ltac case_eq f :=
  generalize (refl_equal f); pattern f at -1; case f.
 
Hint Constructors nd_typing. 
Hint Resolve coercion_sub_rel coerce_non_identity.
Hint Unfold id compose funcompose paircompose.


Lemma non_unique_path_witness: forall sigma d, 
  (ok sigma) ->
  ~(WF_uniquepath d sigma) -> 
  (exists t, exists t', exists m, exists m', 
    coerciongen sigma t d t' m /\
    coerciongen sigma t d t' m' /\
    m <> m' /\ (forall t, m <> (id t)) /\ (forall t, m' <> (id t))).
Proof.
intros sigma d ok_sigma not_wf.
unfold WF_uniquepath in not_wf.
(* UGLY UGLY ... how to do this programmatically? *)
destruct (not_all_ex_not _ _ not_wf) as [a rest1].
destruct (not_all_ex_not _ _ rest1) as [s rest2].
destruct (not_all_ex_not _ _ rest2) as [s' rest3].
destruct (not_all_ex_not _ _ rest3) as [C1 rest4].
destruct (not_all_ex_not _ _ rest4) as [C2 rest5].
destruct (not_all_ex_not _ _ rest5) as [pi rest].
clear not_wf rest1 rest2 rest3 rest4 rest5.
exists s; exists s'; exists C1; exists C2.
destruct (imply_to_and _ _ rest) as [inpi rest1].
destruct (imply_to_and _ _ rest1) as [cg1 rest2].
destruct (imply_to_and _ _ rest2) as [cg2 rest3].
clear rest rest1 rest2.
repeat split;
  (unfold coerciongen; eauto) || idtac.
Case "C1 <> id".
intro t.
unfold not; intro C_eq_id.
subst.
assert ((s=s') /\ (s' = t)) as s_eq_s'.
  eauto using identity_coercions_equate_types.
destruct s_eq_s'; subst.
assert ((t=t) /\ (C2 = (id t))).
  unfold id. eauto using cycles_are_identity.
intuition.
Case "C2 <> id".
intro t.
unfold not; intro C_eq_id.
subst.
assert ((s=s') /\ (s' = t)) as s_eq_s'.
  eauto using identity_coercions_equate_types.
destruct s_eq_s'; subst.
assert ((t=t) /\ (C1 = (id t))).
  unfold id. eauto using cycles_are_identity.
intuition.
Qed.
 
Lemma non_unique_pair_witness: forall sigma d, 
  (ok sigma) -> 
  ~(WF_to_uniquepair d sigma) -> 
  (exists t, exists t1, exists t2, exists s1, exists s2, exists m, exists m', 
    coerciongen sigma t d (typ_pair t1 t2) m /\
    coerciongen sigma t d (typ_pair s1 s2) m' /\
    (m <> m' /\ ((forall t, m <> (id t)) \/ (forall t, m' <> (id t))))).
Proof.
intros sigma d ok_sigma not_wf.
unfold WF_to_uniquepair in not_wf.
(* UGLY UGLY ... how to do this programmatically? *)
destruct (not_all_ex_not _ _ not_wf) as [a rest1].
destruct (not_all_ex_not _ _ rest1) as [s rest2].
destruct (not_all_ex_not _ _ rest2) as [s1 rest3].
destruct (not_all_ex_not _ _ rest3) as [s1' rest4].
destruct (not_all_ex_not _ _ rest4) as [s2 rest5].
destruct (not_all_ex_not _ _ rest5) as [s2' rest6].
destruct (not_all_ex_not _ _ rest6) as [C rest7].
destruct (not_all_ex_not _ _ rest7) as [C' rest8].
destruct (not_all_ex_not _ _ rest8) as [pi rest].
clear not_wf rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8.
exists s; exists s1; exists s2; exists s1'; exists s2'; exists C; exists C'.
destruct (imply_to_and _ _ rest) as [inpi rest1].
destruct (imply_to_and _ _ rest1) as [cg1 rest2].
destruct (imply_to_and _ _ rest2) as [cg2 rest3].
clear rest rest1 rest2.
split.
unfold coerciongen. eauto.
split.
unfold coerciongen. eauto.
destruct (not_and_or _ _ rest3) as [C_neq_C' | rest].
Case "C <> C'".
 split. 
 auto.
 destruct (classic (exists t, C = id t)) as [[t' C_eq_id_t'] | C_neq_id_t].
 SCase "C eq id t'".
   right.
   destruct (classic (exists t, C' = id t)) as [[t'' C'_eq_id_t''] | C'_neq_id_t].
   SSCase "C' = id t''".
   subst.
   assert ((s=(typ_pair s1 s2)) /\ ((typ_pair s1 s2)=t')) as eq1.
     eauto using identity_coercions_equate_types.
   assert ((s=(typ_pair s1' s2')) /\ ((typ_pair s1' s2')=t'')) as eq2.
     eauto using identity_coercions_equate_types.
   destruct eq1 as [eq11 eq12]. destruct eq2 as [eq21 eq22]. subst. injection eq21; intros; subst.
   unfold id in C_neq_C'. eauto.
   SSCase "C' <> id t''".
      apply (not_ex_all_not _ _ C'_neq_id_t).
 SCase "C <> id t".
  left.
  apply (not_ex_all_not _ _ C_neq_id_t).
Case "s1 <> s1' \/ s2 <> s2'".
assert ((typ_pair s1 s2) <> (typ_pair s1' s2')).
  destruct (not_and_or _ _ rest) as [s1_neq_s1' | s2_neq_s2']; injection; intros; eauto.
assert (C <> C') as C_neq_C'.
 eauto using coercion_between_distinct_types.
split. auto.
 destruct (classic (exists t, C = id t)) as [[t' C_eq_id_t'] | C_neq_id_t].
 SCase "C eq id t'".
   right.
   destruct (classic (exists t, C' = id t)) as [[t'' C'_eq_id_t''] | C'_neq_id_t].
   SSCase "C' = id t''".
   subst.
   assert ((s=(typ_pair s1 s2)) /\ ((typ_pair s1 s2)=t')) as eq1.
     eauto using identity_coercions_equate_types.
   assert ((s=(typ_pair s1' s2')) /\ ((typ_pair s1' s2')=t'')) as eq2.
     eauto using identity_coercions_equate_types.
   destruct eq1 as [eq11 eq12]. destruct eq2 as [eq21 eq22]. subst. injection eq21; intros; subst.
   unfold id in C_neq_C'. eauto.
   SSCase "C' <> id t''".
      apply (not_ex_all_not _ _ C'_neq_id_t).
 SCase "C <> id t".
  left.
  apply (not_ex_all_not _ _ C_neq_id_t).
Qed.

Lemma non_nac_app_witness : forall sigma d d',
  ~(WF_app d d' sigma) -> 
  (exists t, exists t1, exists t2, exists s1, exists s2, exists t', exists m1, exists m2, exists m3, exists m4, 
    coerciongen sigma t d (typ_fun t1 t2) m1 /\
    coerciongen sigma t d (typ_fun s1 s2) m2 /\
    coerciongen sigma t' d' t1 m3 /\
    coerciongen sigma t' d' s1 m4 /\
    (t1 <> s1 \/ t2 <> s2)).
Proof.
intros sigma d d' not_wf.
unfold WF_app in not_wf.
(* UGLY UGLY ... how to do this programmatically? *)
destruct (not_all_ex_not _ _ not_wf) as [s rest1].
destruct (not_all_ex_not _ _ rest1) as [s' rest2].
destruct (not_all_ex_not _ _ rest2) as [s1 rest3].
destruct (not_all_ex_not _ _ rest3) as [s2 rest4].
destruct (not_all_ex_not _ _ rest4) as [s3 rest5].
destruct (not_all_ex_not _ _ rest5) as [s4 rest6].
destruct (not_all_ex_not _ _ rest6) as [n1 rest7].
destruct (not_all_ex_not _ _ rest7) as [n2 rest8].
destruct (not_all_ex_not _ _ rest8) as [n3 rest9].
destruct (not_all_ex_not _ _ rest9) as [n4 rest].
clear rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 rest9.
exists s1. exists s2. exists s.
exists s3. exists s'.
exists s4. exists n1. exists n3. exists n2. exists n4.
destruct (imply_to_and _ _ rest) as [cg1 rest1].
destruct (imply_to_and _ _ rest1) as [cg2 rest2].
destruct (imply_to_and _ _ rest2) as [cg3 rest3].
destruct (imply_to_and _ _ rest3) as [cg4 rest4].
clear rest1 rest2 rest3 rest.
pose proof (not_and_or _ _ rest4). intuition.
Qed.
    
Hint Unfold coerciongen.
    
Theorem nonambiguity_core_sufficient : 
  forall sigma gamma e e1 t1 e2 t2 d d',
    (NAC sigma d d') -> 
    (ok sigma) ->
    (ok gamma) -> 
    (nd_typing sigma gamma d d' e e1 t1) -> 
    (nd_typing sigma gamma d d' e e2 t2) -> 
    ((e1,t1) = (e2,t2)).
Proof.
intros until 1. rename H into WF. intros ok_sigma gOK T1 T2.
generalize dependent e2.
generalize dependent t2.
induction T1.
Case "typing_Var". intros.
inversion T2. subst.  assert (t=t2). eauto using binds_id.
subst. eauto.
Case "typing_Base". intros.
inversion T2. subst.  assert (t=t2). eauto using binds_id.
subst. eauto.
Case "typing_Ascription".
intros.
inversion T2. subst. firstorder.
Case "typing_Abs".
intros.
inversion T2. subst.
destruct (freevars_totality e') as [fvs_e' freevars_e'].
destruct (freevars_totality e'0) as [fvs_e'0 freevars_e'0].
pick fresh y.
assert (y `notin` L) as ynotinL.
 fsetdec.
assert (y `notin` L0) as ynotinL0.
 fsetdec.
assert (ok ([(y,t_x)]++G)) as ok_yG.
 rewrite_env ((y,t_x)::G).
 eapply ok_cons; [eauto | fsetdec].
pose proof (H9 y ynotinL0) as typing_e2_body.
pose proof (H0 y ynotinL WF ok_sigma ok_yG _ _ typing_e2_body) as fromIH.
injection fromIH; intros. subst.
assert (e' = e'0). eapply (open_exp_injection e' e'0 y); try eauto || fsetdec.
subst; eauto.
Case "typing_Pair".
intros. inversion T2. subst.
firstorder.
pose proof (H4 _ _ H5) as eq1.
pose proof (H3 _ _ H8) as eq2.
injection eq1. injection eq2. intros; subst; auto.
Case "typing_App".
intros. inversion T2. subst.
pose proof (IHT1_1 WF ok_sigma gOK _ _ H3) as e1_eq.
pose proof (IHT1_2 WF ok_sigma gOK _ _ H4) as e2_eq.
injection e1_eq; injection e2_eq; intros; subst.
clear IHT1_1 IHT1_2 e1_eq e2_eq.
rename e1'0 into e1'.
rename e2'0 into e2'.
unfold NAC in WF.
destruct WF as [WF_up_prim [WF_up_sub [WF_upair WF_a]]].
unfold WF_app in WF_a.
destruct (WF_a _ _ _ _ _ _ _ _ _ _ H H0 H9 H12) as [targ_eq tret_eq].
subst.
clear WF_a WF_upair.
unfold WF_uniquepath in WF_up_prim.
  unfold coerciongen in H, H9.
  assert (m1=m0). eauto.
unfold WF_uniquepath in WF_up_sub.
  unfold coerciongen in H0, H12.
  assert (m2=m3). eauto.
subst. auto.
Case "typing_Proj One".
intros. inversion T2. subst.
firstorder.
pose proof (H5 _ _ H1) as fromIH.
injection fromIH; intros; subst.
rename e'0 into e'.
rename H0 into WF_up. rename H3 into WF_upair.
unfold WF_to_uniquepair in  WF_upair.
   unfold coerciongen in H6, H.
   assert (m=m0 /\ t1=t0 /\ t2=t5) as eqs. eauto.
destruct eqs as [eq1 [eq2 eq3]]. subst. auto.
Case "typing_Proj Two".
intros. inversion T2. subst.
firstorder.
pose proof (H5 _ _ H1) as fromIH.
injection fromIH; intros; subst.
rename e'0 into e'. 
rename H0 into WF_up. rename H3 into WF_upair.
unfold WF_to_uniquepair in  WF_upair.
   unfold coerciongen in H6, H.
   assert (m=m0 /\ t1=t4 /\ t2=t0) as eqs. eauto.
destruct eqs as [eq1 [eq2 eq3]]. subst. auto.
Qed.

Lemma nonamb_core_necessary_not_uniquepath_right: 
  forall sigma d d', 
    (ok sigma) ->
    ~(WF_uniquepath d' sigma) -> 
    (exists gamma, exists e, exists e1, exists e2, exists t1, exists t2, 
      nd_typing sigma gamma d d' e e1 t1 /\
      nd_typing sigma gamma d d' e e2 t2 /\
      (e1 <> e2 \/ t1 <> t2)).
Proof.
intros sigma d d' ok_sigma not_wf_up.
 destruct (non_unique_path_witness _ _ ok_sigma not_wf_up) as [t [t' [m [m' [C_m [C_m' [m_neq_m' [m_neq_id m'_neq_id]]]]]]]].
 pick fresh f.
 pick fresh x.
 exists ([(f, (typ_fun t' t'))]++[(x, t)]).
 exists (exp_app (exp_fvar f) (exp_fvar x)).
 exists (exp_app (coerce (id (typ_fun t' t')) (exp_fvar f)) (coerce m (exp_fvar x))).
 exists (exp_app (coerce (id (typ_fun t' t')) (exp_fvar f)) (coerce m' (exp_fvar x))).
 exists t'. exists t'.
 split. 
 SCase "nd_typing 1". unfold id.
   induction d; eapply nd_typing_App; eauto.
 split.
 SCase "nd_typing 2". unfold id.
   induction d; eapply nd_typing_App; eauto.
 SCase "neq". left. simpl.
   rewrite (coerce_non_identity m (exp_fvar x) m_neq_id).
   rewrite (coerce_non_identity m' (exp_fvar x) m'_neq_id).
   injection; eauto.
Qed.





Lemma nonamb_core_necessary_not_uniquepath_left: 
  forall sigma d d', 
    (ok sigma) ->
    ~(WF_uniquepath d sigma) -> 
    (exists gamma, exists e, exists e1, exists e2, exists t1, exists t2, 
      nd_typing sigma gamma d d' e e1 t1 /\
      nd_typing sigma gamma d d' e e2 t2 /\
      (e1 <> e2 \/ t1 <> t2)).
Proof.
intros sigma d d' ok_sigma not_wf_up.
 destruct (classic (d=d')) as [d_eq_d' | d_neq_d'].
 subst. eauto using nonamb_core_necessary_not_uniquepath_right.
 Case "d <> d'".
 induction d.
   SCase "d = RelPrim".
     induction d'. destruct d_neq_d'; eauto. 
     SSCase "d' = RelSub". clear d_neq_d'.
      destruct (non_unique_path_witness _ _ ok_sigma not_wf_up) as [t [t' [m [m' [C_m [C_m' [m_neq_m' [m_neq_id m'_neq_id]]]]]]]].
      assert (coerciongen sigma t RelPrim t' m) as C_m_sub.
          unfold coerciongen in *; eauto using coercion_sub_rel.
      assert (coerciongen sigma t RelPrim t' m') as C_m'_sub.
          unfold coerciongen in *; eauto using coercion_sub_rel.
      pick fresh f.
      pick fresh x.
      exists ([(f, (typ_fun t' t'))]++[(x, t)]).
      exists (exp_app (exp_fvar f) (exp_fvar x)).
      exists (exp_app (coerce (id (typ_fun t' t')) (exp_fvar f)) (coerce m (exp_fvar x))).
      exists (exp_app (coerce (id (typ_fun t' t')) (exp_fvar f)) (coerce m' (exp_fvar x))).
      exists t'. exists t'.
      split. 
      SSSCase "nd_typing 1". unfold id.
        eapply nd_typing_App; eauto.
        split.
      SSSCase "nd_typing 2". unfold id.
        eapply nd_typing_App; eauto.
      SSSCase "neq". left. simpl.
        rewrite (coerce_non_identity m (exp_fvar x) m_neq_id).
        rewrite (coerce_non_identity m' (exp_fvar x) m'_neq_id).
        injection; eauto.
  SCase "d=RelSub".
      induction d'. 
      SSCase "d'=RelPrim".
      destruct (non_unique_path_witness _ _ ok_sigma not_wf_up) as [t [t' [m [m' [C_m [C_m' [m_neq_m' [m_neq_id m'_neq_id]]]]]]]].
      pick fresh f.
      pick fresh x.
      exists ([(f, (typ_fun t t))]++[(x, t)]).
      exists (exp_app (exp_fvar f) (exp_fvar x)).
      exists (exp_app (coerce (compose (typ_fun t t) (id (typ_fun t t'))
                                  (funcompose (typ_fun t t) t (id t) m)) 
                       (exp_fvar f)) 
                       (coerce (id t) (exp_fvar x))).
      exists (exp_app (coerce (compose (typ_fun t t) (id (typ_fun t t'))
                                  (funcompose (typ_fun t t) t (id t) m')) 
                       (exp_fvar f)) 
                       (coerce (id t) (exp_fvar x))).
      exists t'. exists t'.
      split.
      SSSCase "nd_typing 1". 
        unfold coerciongen in *.
        eapply nd_typing_App; try solve [unfold coerciongen in *; eauto].
        unfold coerciongen.  eapply coercion_FunTrans.
           assert (~In (typ_fun t t') [typ_fun t t]) as HH.
             assert (t <> t') as t_neq_t'. eapply (nonidentity_implies_inequality sigma ([t])); eauto.
             eapply not_in_singleton. unfold not; intros. injection H; intros; subst; eauto.
           apply HH. unfold id; eauto. eauto. unfold id; eauto. unfold id; eauto.
      split.
      SSSCase "nd_typing 2". 
        unfold coerciongen in *.
        eapply nd_typing_App; try solve [unfold coerciongen in *; eauto].
        unfold coerciongen.  eapply coercion_FunTrans.
           assert (~In (typ_fun t t') [typ_fun t t]) as HH.
             assert (t <> t') as t_neq_t'. eapply (nonidentity_implies_inequality sigma ([t])); eauto.
             eapply not_in_singleton. unfold not; intros. injection H; intros; subst; eauto.
           apply HH. unfold id; eauto. eauto. unfold id; eauto. unfold id; eauto.
       left. simpl. unfold compose. unfold funcompose. simpl. unfold not. intros HH.
       injection HH. eauto.
     SSCase "d' = RelSub".  
       destruct d_neq_d'. eauto.
Qed.
  

Theorem nonambiguity_core_necessary :
  forall sigma d d',
    (ok sigma) ->
    ~(NAC sigma d d') ->
    (exists gamma, exists e, exists e1, exists e2, exists t1, exists t2, 
      nd_typing sigma gamma d d' e e1 t1 /\
      nd_typing sigma gamma d d' e e2 t2 /\
      (e1 <> e2 \/ t1 <> t2)).
Proof.
intros sigma d d' ok_sigma nac.
unfold NAC in nac.
destruct (not_and_or _ _ nac) as [not_wf_up | nac_1].
Case "not uniquepath left".
  eauto using nonamb_core_necessary_not_uniquepath_left.  
destruct (not_and_or _ _ nac_1) as [not_wf_up | nac_2].
Case "not uniquepath relsub".
 eauto using nonamb_core_necessary_not_uniquepath_right.
destruct (not_and_or _ _ nac_2) as [not_wf_to_unique_pair | nac_3].  
 clear nac nac_1 nac_2.
Case "not to uniquepair".
 destruct (non_unique_pair_witness _ _ ok_sigma not_wf_to_unique_pair) as [t [t1 [t2 [s1 [s2 [m [m' [C_m [C_m' diseqs]]]]]]]]].
 pick fresh x.
 exists ([(x, t)]).
 exists (exp_proj One (exp_fvar x)).
 exists (exp_proj One (coerce m (exp_fvar x))).
 exists (exp_proj One (coerce m' (exp_fvar x))).
 exists t1. exists s1.
 split.
 SCase "nd_typing 1". eauto.
 split. 
 SCase "nd_typing 2". eauto.
 left.
 destruct diseqs as [m_neq_m' [m_neq_id | m'_neq_id]].
 SSCase "m_neq_id".
 rewrite (coerce_non_identity m (exp_fvar x) m_neq_id).
 destruct (coerce_disjunct m' (exp_fvar x)) as [eq_id | eq_app].
   rewrite eq_id. discriminate.
   rewrite eq_app. injection; eauto.
 SSCase "m'_neq_id".
 rewrite (coerce_non_identity m' (exp_fvar x) m'_neq_id).
 destruct (coerce_disjunct m (exp_fvar x)) as [eq_id | eq_app].
   rewrite eq_id. discriminate.
   rewrite eq_app. injection; eauto.
Case "not unique app".
 clear - nac_3 case ok_sigma.
 destruct (non_nac_app_witness _ _ _ nac_3) as [t [t1 [t2 [s1 [s2 [t' [m1 [m2 [m3 [m4 [cgen_f_1 [cgen_f_2 [cgen_3 [cgen_4 neq_disj]]]]]]]]]]]]]].
 pick fresh f.
 pick fresh x.
 exists ([(f, t)] ++ [(x,t')]).
 exists (exp_app (exp_fvar f) (exp_fvar x)).
 exists (exp_app (coerce m1 (exp_fvar f)) (coerce m3 (exp_fvar x))).
 exists (exp_app (coerce m2 (exp_fvar f)) (coerce m4 (exp_fvar x))).
 exists t2.
 exists s2.
 split.
 SCase "nd_typing 1".
   eapply nd_typing_App; eauto.
 split.
 SCase "nd_typing 2".
   eapply nd_typing_App; eauto.
 SCase "neq".
   destruct neq_disj as [t1_neq_s1 | t2_neq_s2].
   SSCase "t1_neq_s1".
   clear cgen_3 cgen_4.
   left.
   assert (m1 <> m2).
     assert ((typ_fun t1 t2) <> (typ_fun s1 s2)) as fun_neq.
       injection; intros. eauto. 
     unfold coerciongen in cgen_f_1.       
     unfold coerciongen in cgen_f_2.
     eapply (coercion_between_distinct_types sigma ([t]) ([t])); eauto.
     assert (~((t=(typ_fun t1 t2)) /\ (t=(typ_fun s1 s2)))) as not_t_eq_both.
       unfold not; intros eq_both.
       destruct eq_both as [eql eqr].
         subst t. injection eqr. intros; eauto.
     destruct (not_and_or _ _ not_t_eq_both) as [t_neq_t1t2 | t_neq_s1s2].
     SSSCase "t_neq_t1t2".
       assert ((coerce m1 (exp_fvar f)) = (exp_app m1 (exp_fvar f))) as cm1_eq.
       eapply coerce_non_identity.
         unfold coerciongen in cgen_f_1.
         eauto using inequality_implies_nonidentity.
       rewrite cm1_eq.
       destruct (coerce_disjunct m2 (exp_fvar f)) as [cm2l | cm2r].
       rewrite cm2l. discriminate.
       rewrite cm2r. injection; intros; eauto.
     SSSCase "t_neq_s1s2".
       assert ((coerce m2 (exp_fvar f)) = (exp_app m2 (exp_fvar f))) as cm2_eq.
       eapply coerce_non_identity.
         unfold coerciongen in cgen_f_2.
         eauto using inequality_implies_nonidentity.
       rewrite cm2_eq.
       destruct (coerce_disjunct m1 (exp_fvar f)) as [cm1l | cm1r].
       rewrite cm1l. discriminate.
       rewrite cm1r. injection; intros; eauto.
   SSCase "t2_neq_s2".
     right; eauto.
Qed.

