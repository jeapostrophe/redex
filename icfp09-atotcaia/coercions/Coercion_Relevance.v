Require Export Coercion_Ambiguity.
Require Import Classical.
Set Undo 100000.

Hint Constructors coercion typing App.
Hint Unfold coerciongen.
Hint Resolve in_eq in_cons in_inv in_nil insingleton.
Hint Resolve coercion_pi_strengthening.
Hint Resolve altnosub_to_altsub.
Hint Constructors nd_typing. 
Hint Resolve coercion_sub_rel coerce_non_identity.
Hint Unfold id compose funcompose paircompose.
Hint Unfold coerciongen.
Hint Constructors prims.

Lemma not_uniquepath_implies_prims_differ_coercion :
  forall sigma d t t' m1 m2 pi1 pi2 a1 a2 p1 p2, 
    (ok sigma) -> 
    (In t pi1) -> (In t pi2) ->
    (coercion sigma pi1 a1 t d t' m1) -> 
    (coercion sigma pi2 a2 t d t' m2) -> 
    (m1 <> m2) -> 
    (prims m1 p1) -> 
    (prims m2 p2) -> 
    (p1 <> p2).
Proof.
intros until 1. rename H into ok_sigma. 
intros In_pi1 In_pi2 C1 C2 m1_neq_m2 prims1 prims2.
generalize dependent m2.
generalize dependent pi2.
generalize dependent a2.
generalize dependent p1.
generalize dependent p2.
induction C1.
Case "id".
intros.
assert (t=t /\ (m2 = (id t))). unfold id. eauto using cycles_are_identity.
intuition.
Case "prim trans".
intros. 
induction C2.
SCase "C2 is id".
  assert ((t2=t) /\ C =(id t2)). unfold id. eauto using cycles_are_identity, in_cons.
   intuition. subst. intuition.
SCase "C2 is prim trans".
  destruct (classic (f0=f)) as [f0_eq_f | f0_neq_f].
  SSCase "f0 = f".
    subst. clear IHC2.
    assert (typ_fun t1 t2=typ_fun t1 t0) as t1t2_eq_t1t0. clear -H H1 ok_sigma. eauto using binds_id.
    injection t1t2_eq_t1t0. intro t2_eq_t0. subst.
    inversion prims1. subst.
    inversion H6. subst. rename H5 into prims_C1.
    assert (C<>C0) as C_neq_C0. clear - m1_neq_m2. unfold compose in m1_neq_m2. unfold not. intro. subst. destruct m1_neq_m2. eauto.
    inversion prims2. subst. inversion H7. subst. rename H5 into prims_C0.
    pose proof (IHC1 ok_sigma (in_eq _ _) _ _ prims_C1 _ (t0::pi0) (in_eq _ _) _ C2 C_neq_C0 prims_C0) as fromIHC1.
    assert (fvs2 = (singleton f)). clear - H8. inversion H8. inversion H3. subst. inversion H1. fsetdec.
    assert (fvs3 = (singleton f)). clear - H10. inversion H10. inversion H3. subst. inversion H1. fsetdec.
    subst.
    assert (f `notin` fvs1).
       clear - C1 In_pi1 H1.
      SSSCase "f0=f".

        
 
        assert (f0 = f). clear - H H1. eauto using binds_id.

 
  


Admitted.

Lemma not_uniquepath_implies_prims_differ :
  forall sigma d t t' m1 m2 p1 p2, 
    (ok sigma) -> 
    (coerciongen sigma t d t' m1) -> 
    (coerciongen sigma t d t' m2) -> 
    (m1 <> m2) -> 
    (prims m1 p1) -> 
    (prims m2 p2) -> 
    (p1 <> p2).
Proof.
Admitted.
    
Lemma ambiguity_relevant_not_uniquepath: 
  forall sigma d, 
    (ok sigma) ->
    ~(WF_uniquepath d sigma) -> 
    (exists gamma, exists e, exists e1, exists e2, exists t1, exists t2, 
      nd_typing sigma gamma e e1 t1 /\
      nd_typing sigma gamma e e2 t2 /\
      (forall p1 p2,  prims e1 p1 -> prims e2 p2 -> 
        (p1 <> p2 \/ t1 <> t2))).
Proof.
intros sigma d ok_sigma not_wf_up.
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
 SCase "p1 <> p2". intros p1 p2 prims1 prims2. left.
   simpl in prims1, prims2.
   rewrite (coerce_non_identity m (exp_fvar x) m_neq_id) in prims1.
   rewrite (coerce_non_identity m' (exp_fvar x) m'_neq_id) in prims2.
   inversion prims1. subst.
   inversion H1. subst. clear H1.
   inversion prims2. subst.
   inversion H1. subst. clear H1.
   inversion H3. subst. inversion H5. subst. clear H3 H5.
   inversion H4. subst. inversion H5. subst. clear H4 H5.
   assert (fvs1 <> fvs2). eauto using not_uniquepath_implies_prims_differ.
   assert (fvs1 = {} `union` fvs1 `union` {}). fsetdec.
   assert (fvs2 = {} `union` fvs2 `union` {}). fsetdec. 
   rewrite <- H0. rewrite <- H3. eauto.
Qed.


Theorem ambiguity_is_relevant :
  forall sigma,
    (ok sigma) ->
    ~(NAC sigma RelPrim RelSub) ->
    (exists gamma, exists e, exists e1, exists e2, exists t1, exists t2, 
      nd_typing sigma gamma e e1 t1 /\
      nd_typing sigma gamma e e2 t2 /\
      (forall p1 p2,  prims e1 p1 -> prims e2 p2 -> 
        (p1 <> p2 \/ t1 <> t2))).
Proof.
intros sigma ok_sigma nac.
unfold NAC in nac.
destruct (not_and_or _ _ nac) as [not_wf_up | nac_1].
Case "not uniquepath relprim".
 eauto using nonamb_core_necessary_not_uniquepath.  
destruct (not_and_or _ _ nac_1) as [not_wf_up | nac_2].
Case "not uniquepath relsub".
 eauto using nonamb_core_necessary_not_uniquepath.
destruct (not_and_or _ _ nac_2) as [not_wf_to_unique_pair | nac_3].  
 clear nac nac_1 nac_2.
Case "not to uniquepair".
 destruct (non_unique_pair_witness _ _ ok_sigma (refl_equal _) not_wf_to_unique_pair) as [t [t1 [t2 [s1 [s2 [m [m' [C_m [C_m' diseqs]]]]]]]]].
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
