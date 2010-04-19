Require Export Coercion_Infrastructure.
Require Import Classical.
Set Undo 100000.

Definition WF_no_fun_pair r sigma := forall pi pi' t1 t2 s1 s2 a m1 m2, 
  (In (typ_fun t1 t2) pi) -> 
  (In (typ_pair s1 s2) pi') -> 
  ((~ (coercion sigma pi a (typ_fun t1 t2) r (typ_pair s1 s2)) m1) /\
   (~ (coercion sigma pi' a (typ_pair s1 s2) r (typ_fun t1 t2)) m2)).

Definition no_unnecessary_fun_subtyping_path (sigma:Sigma) : Prop := forall t t' t1 t2 C C' theta a, 
  In t theta ->
  (coercion sigma theta a t RelPrim t' C) ->
  (coercion sigma theta a t RelPrim (typ_fun t1 t2) C') -> 
  (forall s1 s2, 
    (typ_fun t1 t2) <> (typ_fun s1 s2) -> 
    (not ((exists C1, coerciongen sigma (typ_fun s1 s2) RelPrim t' C1) /\
      (exists C2, coerciongen sigma (typ_fun t1 t2) RelSub (typ_fun s1 s2) C2)))).

Definition no_unnecessary_pair_subtyping_path (sigma:Sigma) : Prop := forall t t' t1 t2 C C' theta a, 
  In t theta ->
  (coercion sigma theta a t RelPrim t' C) ->
  (coercion sigma theta a t RelPrim (typ_pair t1 t2) C') -> 
  (forall s1 s2, 
    (typ_pair t1 t2) <> (typ_pair s1 s2) -> 
    (not ((exists C1, coerciongen sigma (typ_pair s1 s2) RelPrim t' C1) /\
      (exists C2, coerciongen sigma (typ_pair t1 t2) RelSub (typ_pair s1 s2) C2)))).

Definition no_multiple_fun_subtyping_paths (sigma:Sigma) : Prop := forall t t1 t2 s1 s2 s1' s2' C1 C2 C3 C4, 
  (coerciongen sigma (typ_fun s1 s2) RelPrim t C1) ->
  (coerciongen sigma (typ_fun s1' s2') RelPrim t C2) -> 
  (coerciongen sigma (typ_fun t1 t2) RelSub (typ_fun s1 s2) C3) -> 
  (coerciongen sigma (typ_fun t1 t2) RelSub (typ_fun s1' s2') C4) -> 
  (typ_fun s1 s2) = (typ_fun s1' s2').

Definition no_multiple_pair_subtyping_paths (sigma:Sigma) : Prop := forall t t1 t2 s1 s2 s1' s2' C1 C2 C3 C4, 
  (coerciongen sigma (typ_pair s1 s2) RelPrim t C1) ->
  (coerciongen sigma (typ_pair s1' s2') RelPrim t C2) -> 
  (coerciongen sigma (typ_pair t1 t2) RelSub (typ_pair s1 s2) C3) -> 
  (coerciongen sigma (typ_pair t1 t2) RelSub (typ_pair s1' s2') C4) -> 
  (typ_pair s1 s2) = (typ_pair s1' s2').

Definition no_fun_and_pair_subtyping_paths (sigma:Sigma) : Prop := forall t p1 p2 s1 s2 f1 f2 g1 g2 C1 C2 C3 C4, 
  (coerciongen sigma (typ_pair p1 p2) RelPrim t C1) ->
  (coerciongen sigma (typ_fun f1 f2) RelPrim t C2) -> 
  (coerciongen sigma (typ_pair s1 s2) RelSub (typ_pair p1 p2) C3) -> 
  (coerciongen sigma (typ_fun g1 g2) RelSub (typ_fun f1 f2) C4) -> 
  False.


(* Structural properties of coercion *)
Lemma coercion_sub_rel : forall sigma theta t t' C a, 
  coercion sigma theta a t RelPrim t' C -> 
  coercion sigma theta a t RelSub t' C.
Proof.
intros until 1. rename H into D_1. 
induction D_1.
intros.
  eapply coercion_Id.
intros.
   eauto using coercion_PrimTrans.
intros.
   eauto using coercion_FunTrans.
intros.
   eauto using coercion_PairTrans.
Qed.

Lemma altnosub_to_altsub : forall sigma pi d t t' m a, 
  coercion sigma pi a t d t' m -> 
  coercion sigma pi AltSub t d t' m.
Proof.
intros. rename H into C_nosub.
induction C_nosub; eauto || discriminate.
Qed.

(* Cycle detection lemmas *)
Lemma cycles_are_identity : forall sigma theta t t' C a r,
  In t' theta -> 
  coercion sigma theta a t r t' C ->
  (t = t' /\ C = (exp_lam t (exp_bvar 0))).
intros until 1. intro D.
induction D.
Case "Id".
  auto.
Case "PrimTrans".
destruct (IHD (in_cons _ _ _ H)) as [inTheta Ceq].
subst t2. contradiction.
Case "FunTrans".
destruct (IHD3 (in_cons _ _ _ H)) as [inTheta Ceq].
subst t'. contradiction.
Case "PairTrans".
destruct (IHD3 (in_cons _ _ _ H)) as [inTheta Ceq].
subst t'. contradiction.
Qed.

Hint Resolve in_eq in_cons in_inv in_nil insingleton.

Lemma coercion_between_distinct_types : 
  forall sigma pi1 pi2 a a' t1 t2 s1 s2 m1 m2 d, 
    (ok sigma) ->
    (coercion sigma pi1 a t1 d s1 m1) -> 
    (In t1 pi1) -> 
    (coercion sigma pi2 a' t2 d s2 m2) -> 
    (In t2 pi2) -> 
    ((t1 <> t2) \/ (s1 <> s2)) -> 
    (m1 <> m2).
Proof.
intros until 1. rename H into ok_sigma. intros Cgen1 In_pi1 Cgen2 In_pi2 neq_disj.
generalize dependent pi2.
generalize dependent t2. 
generalize dependent s2.
generalize dependent m2.
generalize dependent a'.
induction Cgen1.
Case "identity 1".
  intros. induction Cgen2; destruct neq_disj; try injection; eauto || discriminate.
Case "trans 1".
  intros.
  induction Cgen2; try solve [unfold compose; unfold funcompose; unfold paircompose; unfold not; intro; discriminate].
  SCase "trans 2". 
    destruct neq_disj as [t1_neq_t0 | t3_neq_t5].
    SSCase "t1_neq_t0".
      assert (f <> f0). eauto.
      unfold compose. injection; intros; eauto.
    SSCase "t3 neq t5".
      assert (C<>C0). 
        eapply IHCgen1; try apply (in_eq t4 pi0); eauto. 
      unfold compose. injection; intros; eauto.
Case "funcompose". intros.
  induction Cgen2; try solve [unfold compose; unfold funcompose; unfold paircompose; unfold not; intro; discriminate].
    SSCase "funcompose".
    destruct neq_disj as [fneq | t'_neq_t'0].
       SSSCase "fneq".
         unfold compose; unfold not; intro. injection H1. intros. subst. eauto.
       SSSCase "t' <> t'0".
         clear IHCgen2_1 IHCgen2_2 IHCgen2_3.
         assert (C' <> C'0) as C'_neq.
             eapply IHCgen1_3. eauto. eauto. right. apply t'_neq_t'0. apply Cgen2_3. eauto.
         unfold compose; unfold not; intro. injection H1. intros. subst. eauto.
Case "pair". intros.
  induction Cgen2; try solve [unfold compose; unfold funcompose; unfold paircompose; unfold not; intro; discriminate].
    SSCase "funcompose".
    destruct neq_disj as [fneq | t'_neq_t'0].
       SSSCase "fneq".
         unfold compose; unfold not; intro. injection H1. intros. subst. eauto.
       SSSCase "t' <> t'0".
         clear IHCgen2_1 IHCgen2_2 IHCgen2_3.
         assert (C' <> C'0) as C'_neq.
             eapply IHCgen1_3. eauto. eauto. right. apply t'_neq_t'0. apply Cgen2_3. eauto.
         unfold compose; unfold not; intro. injection H1. intros. subst. eauto.
Qed.

Lemma identity_coercions_equate_types : forall sigma pi a d t1 t2 t3, 
  coercion sigma pi a t1 d t2 (id t3) -> 
  t1 = t2 /\ t2 = t3.
Proof.
  intros.
remember (id t3) as id_t3.
induction H; unfold id in Heqid_t3; try discriminate; injection Heqid_t3; intros; subst. eauto.
Qed.


Lemma identity_implies_equality : forall sigma pi a t d t' C, 
  (In t pi) -> 
  (coercion sigma pi a t d t' C) -> 
  (C = id t) -> 
  t = t'.
Proof.
intros. rename H into inPi. rename H0 into Cgen. rename H1 into Ceq. 
induction Cgen; try solve [unfold id; unfold compose; unfold funcompose; unfold paircompose; simpl; eauto || discriminate].
Qed.

Lemma nonidentity_implies_inequality: forall sigma theta t t' C a d, 
  (In t theta) -> 
  (coercion sigma theta a t d t' C) -> 
  C <> (id t) -> 
  t <> t'.
Proof. 
intros until 1. rename H into inTheta. intros D Cneq.
unfold id in Cneq.
induction D.
Case "coercion_Id".
destruct Cneq. auto.
Case "coercion_PrimTrans".
unfold not. intro t1eq.
subst t1.
destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ inTheta) D) as [t2Eqt3 CeqId].
subst t2. contradiction.
Case "funtrans".
destruct (classic (C1 = (id t1'))).
  SCase "C1 = id t1'".
    assert (t1' = t1). eauto using identity_implies_equality.
    subst.
    destruct (classic (C2 = (id t2))).
      SSCase "C2 = id t2".
        assert (t2=t2'). eauto using identity_implies_equality.
        subst. eauto. (* contradicts not in *)
      SSCase "C2 <> id".
        assert (t2 <> t2'). unfold id in *; eauto.
        unfold not. intro. subst.
        assert (In (typ_fun t1 t2) (typ_fun t1 t2'::pi)) as in_ext. eauto.
        destruct (cycles_are_identity _ _ _ _ _ _ _ in_ext D3) as [feq Ceq'].
        injection feq; intros. eauto.
   SCase "C2 <> id".
      assert (t1' <> t1). unfold id in *; eauto.
        unfold not. intro. subst.
        assert (In (typ_fun t1 t2) (typ_fun t1' t2'::pi)) as in_ext. eauto.
        destruct (cycles_are_identity _ _ _ _ _ _ _ in_ext D3) as [feq Ceq'].
        injection feq; intros. eauto.
Case "pairtrans".
destruct (classic (C1 = (id t1))).
  SCase "C1 = id t1'".
    assert (t1 = t1'). eauto using identity_implies_equality.
    subst.
    destruct (classic (C2 = (id t2))).
      SSCase "C2 = id t2".
        assert (t2=t2'). eauto using identity_implies_equality.
        subst. eauto. (* contradicts not in *)
      SSCase "C2 <> id".
        assert (t2 <> t2'). unfold id in *; eauto.
        unfold not. intro. subst.
        assert (In (typ_pair t1' t2) (typ_pair t1' t2'::pi)) as in_ext. eauto.
        destruct (cycles_are_identity _ _ _ _ _ _ _ in_ext D3) as [feq Ceq'].
        injection feq; intros. eauto.
   SCase "C2 <> id".
      assert (t1 <> t1'). unfold id in *; eauto.
        unfold not. intro. subst.
        assert (In (typ_pair t1 t2) (typ_pair t1' t2'::pi)) as in_ext. eauto.
        destruct (cycles_are_identity _ _ _ _ _ _ _ in_ext D3) as [feq Ceq'].
        injection feq; intros. eauto.
Qed.

Lemma inequality_implies_nonidentity: forall sigma theta t t' C a d, 
  (In t theta) ->
  (t <> t') -> 
  (coercion sigma theta a t d t' C) -> 
  (forall s, C <> id s).
Proof.
intros until 1. rename H into inTheta. intros t_neq_t' Cgen.
induction Cgen; intros; try eauto; unfold compose; unfold id; discriminate.
Qed.


(* Other structural properties *)

Lemma relsub_derivations_use_subtyping_atmost_once:  forall sigma t t' C pi a, 
  (WF_to_uniquefunc RelPrim sigma) -> 
  (WF_to_uniquepair RelPrim sigma) -> 
  (WF_no_fun_pair RelPrim sigma) -> 
  (In t pi) -> 
  (coercion sigma pi a t RelSub t' C) -> 
  ((coercion sigma pi a t RelPrim t' C) \/
    (exists t1, exists t2, exists s1, exists s2, exists C1, exists C2, exists C3, exists pi', 
      (typ_fun t1 t2) <> (typ_fun s1 s2) /\
      (In (typ_fun s1 s2) pi') /\
      (C1 = (id t) -> a = AltSub) /\ (* needed to strengthen IH *)
      (coercion sigma pi a t RelPrim (typ_fun t1 t2) C1) /\
      (coerciongen sigma (typ_fun t1 t2) RelSub (typ_fun s1 s2) C2) /\
      (coercion sigma pi' AltNoSub (typ_fun s1 s2) RelPrim t' C3)) \/
    (exists t1, exists t2, exists s1, exists s2, exists C1, exists C2, exists C3, exists pi', 
      (typ_pair t1 t2) <> (typ_pair s1 s2) /\
      (In (typ_pair s1 s2) pi') /\
      (C1 = (id t) -> a = AltSub) /\ (* needed to strengthen IH *)
      (coercion sigma pi a t RelPrim (typ_pair t1 t2) C1) /\
      (coerciongen sigma (typ_pair t1 t2) RelSub (typ_pair s1 s2) C2) /\
      (coercion sigma pi' AltNoSub (typ_pair s1 s2) RelPrim t' C3))).
Proof.
intros until 1. rename H into WF_ufunc. intros WF_upair WF_no_fp tInPi cgenSub. 
induction cgenSub.
Case "cgenSub is C-Id". 
left. unfold coerciongen. eapply coercion_Id.
Case "cgenSub is C-PrimTrans".
assert (In t2 (t2::pi)) as inT2.  eapply in_eq.
pose proof (IHcgenSub WF_ufunc WF_upair WF_no_fp inT2) as fromIH.  
clear IHcgenSub.
destruct fromIH as [relprim | [relsubFun | relsubPair]].
  SCase "relprim".
  left. 
  eapply coercion_PrimTrans; eauto.
  SCase "relsub fun".
  right. left.
  destruct relsubFun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [aalt [Ineq [ inTheta [D2_2_1 [D2_2_2 D2_2_3]]]]]]]]]]]]].
  exists T1. exists T2. exists S1. exists S2.
  exists (compose t1 B1 (exp_base f)).
  exists B2.
  exists B3.
  exists theta'.
  split. 
    SSCase "t1 -> t2 <> s1 -> s2".
    eauto.
  split.
    SSCase "s1 -> s2 in Theta'".
    eauto.
  split.
    SSCase "id t1 -> AltSub".
    intros. unfold compose in H1. discriminate.
  split.
    SSCase "prim".
    eapply coercion_PrimTrans; eauto.
    repeat (split; eauto).
  SCase "relsub pair (similar)".
  right. right.
  destruct relsubPair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [aalt [Ineq [ inTheta [D2_2_1 [D2_2_2 D2_2_3]]]]]]]]]]]]].
  exists T1. exists T2. exists S1. exists S2.
  exists (compose t1 B1 (exp_base f)).
  exists B2.
  exists B3.
  exists theta'.
  split. 
    SSCase "t1 -> t2 <> s1 -> s2".
    eauto.
  split.
    SSCase "s1 -> s2 in Theta'".
    eauto.
  split.
    SSCase "id t1 -> AltSub".
    intros. unfold compose in H1. discriminate.
  split.
    eapply coercion_PrimTrans; eauto.
    repeat (split; eauto).
Case "D2 is C-FunTrans".
right. left.
clear IHcgenSub1 IHcgenSub2.
exists t1. exists t2.
exists t1'. exists t2'.
exists (id (typ_fun t1 t2)).
exists (compose (typ_fun t1 t2) (id (typ_fun t1' t2')) (funcompose (typ_fun t1 t2) t1' C1 C2)).
exists C'.
exists (typ_fun t1' t2'::pi).
split.
  SCase "t1 -> t2 <> t1' -> t2'".
     Lemma inequality_from_list_membership : forall T (a:T) (b:T) l, 
         (In a l) -> (~In b l) -> a <> b.
       intros. unfold not. intros. subst b. contradiction.
     Qed.
  eapply inequality_from_list_membership; eauto.
  split.
  SCase "In theta".
    eapply in_eq.
  split.
  SCase "id t => AltSub".
    intro. auto.
  split.
  SCase "Left Streak 1".
  unfold id.
  eapply coercion_Id; eauto.
  split.
  SCase "Middle Fun Trans".
  unfold coerciongen.
  eapply coercion_FunTrans. 
    SSCase "Premise NotIn singleton".
    pose proof (inequality_from_list_membership _ _ _ _ tInPi H) as ineq.
    unfold not. intros.
    destruct (in_inv H0) as [teq | innil].
    unfold not in ineq. 
    apply ineq; apply teq.
    contradiction.
    SSCase "Premise D2_1".
    auto.
    SSCase "Premise D2_2".
    auto.
    SSCase "Premise Id tail".
    unfold id.
    eapply coercion_Id.
  SCase "Right Streak 1".
    destruct (IHcgenSub3 WF_ufunc WF_upair WF_no_fp (in_eq _ _)) as [relprim | [relsubfun | relsubpair]].
    SSCase "sfx is prim".
      assumption.
    SSCase "sfx is relsub fun (violates to_unique_func)".
      clear IHcgenSub3.
      destruct relsubfun as [s1 [s2 [u1 [u2 [D1 [D2 [D3 [pi' [tneq [in_pi [altsub_imp [pfx [sub sfx]]]]]]]]]]]]].
      clear - altsub_imp WF_ufunc pfx case subcase subsubcase.
      assert (typ_fun t1' t2' = typ_fun s1 s2) as teq.
        pose proof (coercion_Id sigma (typ_fun t1' t2'::pi) AltNoSub RelPrim (typ_fun t1' t2')) as tfun_id.
        unfold WF_to_uniquefunc in WF_ufunc.
        destruct (WF_ufunc _ _ _ _ _ _ _ _ (typ_fun t1' t2'::pi) (in_eq _ _) tfun_id pfx) as [AA [BB CC]].
        subst. auto.
      rewrite <- teq in pfx.
      destruct (cycles_are_identity _ _ _ _ _ _ _ (in_eq _ _) pfx).
      subst D1. 
      unfold id in altsub_imp.
      pose proof (altsub_imp (refl_equal _)). discriminate.
    SSCase "sfx is relsub pair (violates no_func_pair)".
      clear IHcgenSub3.
      destruct relsubpair as [s1 [s2 [u1 [u2 [D1 [D2 [D3 [pi' [tneq [in_pi [altsub_imp [pfx [sub sfx]]]]]]]]]]]]].
      clear - WF_no_fp pfx case subcase subsubcase.
      unfold WF_no_fun_pair in WF_no_fp.
      destruct (WF_no_fp  (typ_fun t1' t2'::pi) (typ_pair s1 s2::pi) t1' t2' s1 s2 AltNoSub D1 D1 (in_eq _ _) (in_eq _ _)).
      contradiction.

Case "D2 is C-PairTrans (similar)".
right. right.
clear IHcgenSub1 IHcgenSub2.
exists t1. exists t2.
exists t1'. exists t2'.
exists (id (typ_pair t1 t2)).
exists (compose (typ_pair t1 t2) (id (typ_pair t1' t2')) (paircompose t1 t2 C1 C2)).
exists C'.
exists (typ_pair t1' t2'::pi).
split.
  SCase "t1 * t2 <> t1' * t2'".
  eapply inequality_from_list_membership; eauto.
  split.
  SCase "In theta".
    eapply in_eq.
  split.
  SCase "id t => AltSub".
    intro. auto.
  split.
  SCase "Left Streak 1".
  unfold id.
  eapply coercion_Id; eauto.
  split.
  SCase "Middle Pair Trans".
  unfold coerciongen.
  eapply coercion_PairTrans. 
    SSCase "Premise NotIn singleton".
    pose proof (inequality_from_list_membership _ _ _ _ tInPi H) as ineq.
    unfold not. intros.
    destruct (in_inv H0) as [teq | innil].
    unfold not in ineq. 
    apply ineq; apply teq.
    contradiction.
    SSCase "Premise D2_1".
    auto.
    SSCase "Premise D2_2".
    auto.
    SSCase "Premise Id tail".
    unfold id.
    eapply coercion_Id.
  SCase "Right Streak 1".
    destruct (IHcgenSub3 WF_ufunc WF_upair WF_no_fp (in_eq _ _)) as [relprim | [relsubfun | relsubpair]].
    SSCase "sfx is prim".
      assumption.
    SSCase "sfx is relsub fun (violates no_pair_func)".
      clear IHcgenSub3.
      destruct relsubfun as [s1 [s2 [u1 [u2 [D1 [D2 [D3 [pi' [tneq [in_pi [altsub_imp [pfx [sub sfx]]]]]]]]]]]]].
      clear - WF_no_fp pfx case subcase subsubcase.
      unfold WF_no_fun_pair in WF_no_fp.
      destruct (WF_no_fp  (typ_fun s1 s2::pi) (typ_pair t1' t2'::pi) s1 s2 t1' t2' AltNoSub D1 D1 (in_eq _ _) (in_eq _ _)).
      contradiction.
    SSCase "sfx is relsub pair (violates to_unique_pair)".
      clear IHcgenSub3.
      destruct relsubpair as [s1 [s2 [u1 [u2 [D1 [D2 [D3 [pi' [tneq [in_pi [altsub_imp [pfx [sub sfx]]]]]]]]]]]]].
      clear - altsub_imp WF_upair pfx case subcase subsubcase.
      assert (typ_pair t1' t2' = typ_pair s1 s2) as teq.
        pose proof (coercion_Id sigma (typ_pair t1' t2'::pi) AltNoSub RelPrim (typ_pair t1' t2')) as tpair_id.
        unfold WF_to_uniquepair in WF_upair.
        destruct (WF_upair _ _ _ _ _ _ _ _ (typ_pair t1' t2'::pi) (in_eq _ _) tpair_id pfx) as [AA [BB CC]].
        subst. auto.
      rewrite <- teq in pfx.
      destruct (cycles_are_identity _ _ _ _ _ _ _ (in_eq _ _) pfx).
      subst D1. 
      unfold id in altsub_imp.
      pose proof (altsub_imp (refl_equal _)). discriminate.
Qed.



Lemma from_uniquefunc_implies_nomul : forall sigma, 
  WF_from_uniquefunc RelPrim sigma -> 
  no_multiple_fun_subtyping_paths sigma.
Proof.
intros.
unfold WF_from_uniquefunc in H.
unfold no_multiple_fun_subtyping_paths; intros.
assert (C1 = C2 /\ s1 = s1' /\ s2 = s2'). 
  eapply H; eauto.
destruct H4 as [A [B C]]; subst; auto.
Qed.


Lemma relprim_sub_alt_ix : forall sigma pi a a' t t' m, 
  (coercion sigma pi a t RelPrim t' m) -> 
  (coercion sigma pi a' t RelPrim t' m).
Proof.
  intros.
  remember RelPrim as rp.
  induction H.
  eapply coercion_Id; eauto.
  eapply coercion_PrimTrans; eauto.
  discriminate. discriminate.
Qed.


Lemma wf_uniquepath_2 : forall sigma, 
  (ok sigma) -> 
  (WF_to_uniquefunc RelPrim sigma) -> 
  (WF_to_uniquepair RelPrim sigma) -> 
  (WF_uniquepath RelPrim sigma) -> 
  (WF_no_fun_pair RelPrim sigma) ->
  (no_unnecessary_fun_subtyping_path sigma) -> 
  (no_unnecessary_pair_subtyping_path sigma) -> 
  (no_multiple_fun_subtyping_paths sigma) ->
  (no_multiple_pair_subtyping_paths sigma) ->
  (no_fun_and_pair_subtyping_paths sigma) ->
  (forall t t' theta C C' a a', In t theta -> 
    coercion sigma theta a t RelSub t' C -> 
    coercion sigma theta a' t RelSub t' C' -> 
    C = C').
intros sigma okSigma WF_f_1 WF_p_1 WF_up_1 WF_no_fp No_un_f No_un_p No_mul_f No_mul_p No_f_and_p.
intros until 1. intros D1 D2.
remember RelSub as rs.
generalize dependent C'.
generalize dependent a'.
induction D1.
Case "D1 is C-Id".
intros a' C' D2.
induction D2.
 SCase "D2 is C-Id".
  auto.
 SCase "D2 is C-PrimTrans".
  destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ H) D2) as [C1 C2].
   subst t2. contradiction.
 SCase "D2 is FunTrans".
  destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ H) D2_3) as [Eq1 Eq2].
  subst t'. contradiction.
 SCase "D2 is PairTrans".
  destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ H) D2_3) as [Eq1 Eq2].
  subst t'. contradiction.
Case "D1 is C-PrimTrans".
intros.
induction D2.
 SCase "Symmetric D2 is C-Id".
  destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ H) D1) as [C1 C2].
   subst t2. contradiction.
 SCase "D2 is C-PrimTrans".
  subst r.
  pose proof (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1) as D1_LR.
  destruct D1_LR as [D1prim | [D1_fun | D1_pair]].
  SSCase "D1 is a level 1 derivation".
  assert (coercion sigma pi a t1 RelPrim t3 (compose t1 C (exp_base f))) as D1_L1.
    eapply coercion_PrimTrans; eauto.

  pose proof (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2) as D2_LR.
  destruct D2_LR as [D2prim | [D2_fun | D2_pair]].
  SSSCase "D2 is a level 1 derivation". 
  unfold WF_uniquepath, coerciongen in WF_p_1. 
  assert (coercion sigma pi a t1 RelPrim t3 (compose t1 C0 (exp_base f0))) as D2_L1.
    eauto using coercion_PrimTrans.
  eapply WF_up_1; eauto using in_eq.
  SSSCase "D2 uses fun subtyping".
    destruct D2_fun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D2_Ineq [InTheta' [altsub_imp [D2_R_Pfx [D2_R_FunSub D2_R_Sfx]]]]]]]]]]]]].
    unfold no_unnecessary_fun_subtyping_path, coerciongen in No_un_f.
    rename f0 into g.
    assert (coercion sigma pi a t1 RelPrim (typ_fun T1 T2) (compose t1 B1 (exp_base g))) as D2_R_Pfx_g.
      eapply coercion_PrimTrans; eauto.
    pose proof (No_un_f _ _ _ _ _ _ _ _ H D1_L1 D2_R_Pfx_g S1 S2 D2_Ineq) as from_No_Un.
    unfold not in from_No_Un.
    assert ((exists C1, coercion sigma [typ_fun S1 S2] AltSub  (typ_fun S1 S2) RelPrim t3 C1) /\
            (exists C2, coercion sigma [typ_fun T1 T2] AltSub  
                       (typ_fun T1 T2) RelSub (typ_fun S1 S2) C2)) as forContra.
    split.
    SSSSCase "Assertion Left". 
      exists B3.
      eapply coercion_pi_strengthening.
      eauto using D2_R_Sfx, relprim_sub_alt_ix.
      apply (insingleton typ (typ_fun S1 S2) theta' InTheta').
    SSSSCase "Assertion Right". 
      exists B2.
      unfold coerciongen in D2_R_FunSub; eauto.
    destruct (from_No_Un forContra).
  SSSCase "D2 uses pair subtyping".
    destruct D2_pair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D2_Ineq [InTheta' [altsub_imp [D2_R_Pfx [D2_R_PairSub D2_R_Sfx]]]]]]]]]]]]].
    unfold no_unnecessary_pair_subtyping_path, coerciongen in No_un_p.
    rename f0 into g.
    assert (coercion sigma pi a t1 RelPrim (typ_pair T1 T2) (compose t1 B1 (exp_base g))) as D2_R_Pfx_g.
      eapply coercion_PrimTrans; eauto.
    pose proof (No_un_p _ _ _ _ _ _ _ _ H D1_L1 D2_R_Pfx_g S1 S2 D2_Ineq) as from_No_Un.
    unfold not in from_No_Un.
    assert ((exists C1, coercion sigma [typ_pair S1 S2] AltSub  (typ_pair S1 S2) RelPrim t3 C1) /\
            (exists C2, coercion sigma [typ_pair T1 T2] AltSub  
                       (typ_pair T1 T2) RelSub (typ_pair S1 S2) C2)) as forContra.
    split.
    SSSSCase "Assertion Left". 
      exists B3.
      eapply coercion_pi_strengthening.
      eauto using D2_R_Sfx, relprim_sub_alt_ix.
      apply (insingleton typ (typ_pair S1 S2) theta' InTheta').
    SSSSCase "Assertion Right". 
      exists B2.
      unfold coerciongen in D2_R_PairSub; eauto.
    destruct (from_No_Un forContra).
 SSCase "D1 uses fun subtyping".
  destruct D1_fun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_Ineq [InTheta' [altsub_imp [D1_R_Pfx [D1_R_FunSub D1_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a t1 RelPrim (typ_fun T1 T2) (compose t1 B1 (exp_base f))) as D1_R_Pfx_f.
    eapply coercion_PrimTrans; eauto.
  pose proof (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2) as D2_LR.
  destruct D2_LR as [D2_prim | [D2_fun | D2_pair]].
 SSSCase "D2 is a level 1 derivation (Symmetric)".
    unfold no_unnecessary_fun_subtyping_path, coerciongen in No_un_f.
    rename f0 into g.
    assert (coercion sigma pi a t1 RelPrim t3 (compose t1 C0 (exp_base g))) as D2_L1.
      eapply coercion_PrimTrans; eauto.
    pose proof (No_un_f _ _ _ _ _ _ _ _ H D2_L1 D1_R_Pfx_f S1 S2 D1_Ineq) as from_No_Un.
    unfold not in from_No_Un.
    assert ((exists C1, coercion sigma [typ_fun S1 S2] AltSub (typ_fun S1 S2) RelPrim t3 C1) /\
           (exists C2, coercion sigma [typ_fun T1 T2] AltSub
                       (typ_fun T1 T2) RelSub (typ_fun S1 S2) C2)) as forContra.
      split.
      SSSSCase "Assertion Left". 
        exists B3.
        eapply coercion_pi_strengthening.
        eauto using D1_R_Sfx, relprim_sub_alt_ix.
        apply (insingleton typ (typ_fun S1 S2) theta' InTheta').
      SSSSCase "Assertion Right". 
        exists B2.
        unfold coerciongen in D1_R_FunSub; eauto.
        destruct (from_No_Un forContra).
      SSSCase "D2 is a fun sub".
        destruct D2_fun as [T1' [T2' [S1' [S2' [B1' [B2' [B3' [theta'' [D2_Ineq [InTheta'' [altsub_imp' [D2_R_Pfx [D2_R_FunSub D2_R_Sfx]]]]]]]]]]]]].
        unfold WF_to_uniquefunc in WF_f_1.
        rename f0 into g.
        assert (coercion sigma pi a t1 RelPrim (typ_fun T1' T2') (compose t1 B1' (exp_base g))) as D2_R_Pfx_g.
          eauto using coercion_PrimTrans.
        pose proof (WF_f_1  _ _ _ _ _ _ _ _ _ H D1_R_Pfx_f D2_R_Pfx_g) as eq.
        destruct eq as [e1 [e2 e3]]. subst T1'. subst T2'. unfold compose in e1. injection e1. intros. subst g. subst B1'. 
        assert (t0 = t2) as t0eqt2.
         assert ((typ_fun t1 t0) = (typ_fun t1 t2)) as inj.
          eapply binds_id; eauto.
          injection inj; intros; auto.
        subst t2.
        assert (C=C0) as Ceq.
         eapply IHD1; eauto using in_eq, relprim_sub_alt_ix.
        subst. auto.
      SSSCase "D2 is a pair sub (violates no fun and pair subtyping paths)".
        destruct D2_pair as [T1' [T2' [S1' [S2' [B1' [B2' [B3' [theta'' [D2_Ineq [InTheta'' [altsub_imp' [D2_R_Pfx [D2_R_PairSub D2_R_Sfx]]]]]]]]]]]]].
        unfold no_fun_and_pair_subtyping_paths, coerciongen in No_f_and_p.
        unfold coerciongen in D2_R_PairSub, D1_R_FunSub.
        assert False as ff.
          eapply (No_f_and_p t3 S1' S2' T1' T2' S1 S2 T1 T2 B3' B3 B2' B2).
            eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply D2_R_Sfx. eauto using insingleton.
            eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply D1_R_Sfx. eauto using insingleton.
            apply D2_R_PairSub.
            apply D1_R_FunSub.
        destruct ff.
 SSCase "D1 is pair sub".
  destruct D1_pair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_Ineq [InTheta' [altsub_imp [D1_R_Pfx [D1_R_PairSub D1_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a t1 RelPrim (typ_pair T1 T2) (compose t1 B1 (exp_base f))) as D1_R_Pfx_f.
    eapply coercion_PrimTrans; eauto.
  pose proof (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2) as D2_LR.
  destruct D2_LR as [D2_prim | [D2_fun | D2_pair]].
  SSSCase "D2 is a level 1 derivation (Symmetric)".
    unfold no_unnecessary_pair_subtyping_path, coerciongen in No_un_p.
    rename f0 into g.
    assert (coercion sigma pi a t1 RelPrim t3 (compose t1 C0 (exp_base g))) as D2_L1.
      eapply coercion_PrimTrans; eauto.
    pose proof (No_un_p _ _ _ _ _ _ _ _ H D2_L1 D1_R_Pfx_f S1 S2 D1_Ineq) as from_No_Un.
    unfold not in from_No_Un.
    assert ((exists C1, coercion sigma [typ_pair S1 S2] AltSub (typ_pair S1 S2) RelPrim t3 C1) /\
           (exists C2, coercion sigma [typ_pair T1 T2] AltSub
                       (typ_pair T1 T2) RelSub (typ_pair S1 S2) C2)) as forContra.
      split.
      SSSSCase "Assertion Left". 
        exists B3.
        eapply coercion_pi_strengthening.
        eauto using D1_R_Sfx, relprim_sub_alt_ix.
        apply (insingleton typ (typ_pair S1 S2) theta' InTheta').
      SSSSCase "Assertion Right". 
        exists B2.
        unfold coerciongen in D1_R_PairSub; eauto.
    destruct (from_No_Un forContra).
  SSSCase "D2 is a fun sub (violates no fun and pair subtyping paths)".
        destruct D2_fun as [T1' [T2' [S1' [S2' [B1' [B2' [B3' [theta'' [D2_Ineq [InTheta'' [altsub_imp' [D2_R_Pfx [D2_R_FunSub D2_R_Sfx]]]]]]]]]]]]].
        unfold no_fun_and_pair_subtyping_paths, coerciongen in No_f_and_p.
        unfold coerciongen in D2_R_FunSub, D1_R_PairSub.
        assert False as ff.
          eapply (No_f_and_p t3 S1 S2 T1 T2 S1' S2' T1' T2').
            eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply D1_R_Sfx. eauto using insingleton.
            eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply D2_R_Sfx. eauto using insingleton.
            apply D1_R_PairSub.
            apply D2_R_FunSub.
        destruct ff.
  SSSCase "D2 is a pair sub(violates no fun and pair subtyping paths)".
    destruct D2_pair as [T1' [T2' [S1' [S2' [B1' [B2' [B3' [theta'' [D2_Ineq [InTheta'' [altsub_imp' [D2_R_Pfx [D2_R_PairSub D2_R_Sfx]]]]]]]]]]]]].
    unfold WF_to_uniquepair in WF_p_1.
    rename f0 into g.
    assert (coercion sigma pi a t1 RelPrim (typ_pair T1' T2') (compose t1 B1' (exp_base g))) as D2_R_Pfx_g.
      eauto using coercion_PrimTrans.
    pose proof (WF_p_1  _ _ _ _ _ _ _ _ _ H D1_R_Pfx_f D2_R_Pfx_g) as eq.
    destruct eq as [e1 [e2 e3]]. subst T1'. subst T2'. unfold compose in e1. injection e1. intros. subst g. subst B1'. 
    assert (t0 = t2) as t0eqt2.
      assert ((typ_fun t1 t0) = (typ_fun t1 t2)) as inj.
        eapply binds_id; eauto.
    injection inj; intros; auto.
    subst t2.
    assert (C=C0) as Ceq.
      eapply IHD1; eauto using in_eq, relprim_sub_alt_ix.
    subst. auto.
  SCase "D2 is C-FunTrans".
  clear IHD2_1 IHD2_2 IHD2_3 IHD1.
  rename D1 into D1_2.
  rename t' into t_final.
  rename t2 into t_mid_1.
  rename t1' into t2.
  rename t0 into t1'.
  assert (typ_fun t1 t1' <> typ_fun t2 t2') as fneq.
  unfold not; intro feq. rewrite <- feq in H2. contradiction.
(*   pose proof (coercion_FunTrans _ _ _ _ _ _ _ _ _ _ H2 D2_1 D2_2 D2_3) as D2. *)
  assert (coercion sigma (typ_fun t2 t2'::pi) AltNoSub (typ_fun t2 t2') RelPrim t_final C') as alreadyUsedSubtyping.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates to_uniquefunc)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_fun t2 t2'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_fun t2 t2' <> typ_fun T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_fun t2 t2'::pi) AltNoSub RelPrim (typ_fun t2 t2')) as forcontra.
          destruct (WF_f_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates no_fun_pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun t2 t2'::pi) (typ_pair T1 T3::pi) t2 t2' T1 T3 AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.
  destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1_2) as [D1_prim | [D1_fun | D1_pair]].
  SSCase "D1_prim ... D1 is level1".
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim  t_final (compose (typ_fun t1 t1') C (exp_base f))) as D1_Contra.
    eapply coercion_PrimTrans; eauto.
  unfold no_unnecessary_fun_subtyping_path, coerciongen in No_un_f.
    pose proof (No_un_f _ _ _ _ _ _ _ _ H D1_Contra (coercion_Id _ _ _ _ _) t2 t2' fneq) as from_Noun.
    assert ((exists C1, coercion sigma [typ_fun t2 t2'] AltSub (typ_fun t2 t2') RelPrim t_final C1) /\
            (exists C2 : exp,  coercion sigma [typ_fun t1 t1'] AltSub 
                    (typ_fun t1 t1') RelSub (typ_fun t2 t2') C2)) as forContra.
  split.
     SSSCase "Assertion Conj left".
     exists C'.
         eapply coercion_pi_strengthening.
         eapply relprim_sub_alt_ix.
         eapply alreadyUsedSubtyping.
         eauto using insingleton, in_eq.
     SSSCase "Assertion Conj right".
     exists (compose (typ_fun t1 t1') (id (typ_fun t2 t2')) (funcompose (typ_fun t1 t1') t2 C1 C2)).
     eapply coercion_FunTrans.
     SSSSCase "Premise not in". 
     unfold not. intros.
       destruct (in_inv H3) as [fEq | inNil]. 
       rewrite fEq in fneq. eapply fneq. reflexivity.
       contradiction.
     SSSSCase "Premise Farg".
       auto.
     SSSSCase "Premise Fret".
       auto.
     SSSSCase "Streak right".
       unfold id. eapply coercion_Id. 
  contradiction.
  SSCase "D1_2_R ... D1 is fun sub".
  destruct D1_fun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D1_2_R_Pfx [D1_2_R_FunSub D1_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim (typ_fun T1 T2) (compose (typ_fun t1 t1') B1 (exp_base f))) as D1_Contra.
   SSSCase "Assertion D1_Contra".
    eapply coercion_PrimTrans; eauto.
   assert (typ_fun t1 t1' <> typ_fun T1 T2) as Tfun_ineq.
    SSSCase "Assertion Tfun_ineq".
     eapply nonidentity_implies_inequality; eauto.
       unfold compose, id. discriminate.
   assert (coercion sigma pi a (typ_fun t1 t1') RelPrim (typ_fun t1 t1') (exp_lam (typ_fun t1 t1') (exp_bvar 0))) as D1_Contra_2.
     eapply coercion_Id;eauto. 
  unfold WF_to_uniquefunc in WF_f_1.
  assert (typ_fun t1 t1' = typ_fun T1 T2) as Contra.
    destruct (WF_f_1 _ _ _ _ _ _ _ _ _ H D1_Contra_2 D1_Contra) as [A1 [A2 A3]].
    subst. auto.
  contradiction.
  SSCase "D1_2_R ... D1 is pair sub".
  destruct D1_pair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D1_2_R_fun_to_pair [D1_2_R_PairSub D1_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim (typ_pair T1 T2) (compose (typ_fun t1 t1') B1 (exp_base f))) as fun_to_pair.
    eauto using coercion_PrimTrans, in_eq.
  unfold WF_no_fun_pair in WF_no_fp.
  destruct (WF_no_fp  pi [typ_pair T1 T2] t1 t1' T1 T2 a (compose (typ_fun t1 t1') B1 (exp_base f)) B1 H (in_eq _ _)).
  contradiction.  

  SCase "D2 is C-PairTrans".
  clear IHD2_1 IHD2_2 IHD2_3 IHD1.
  rename D1 into D1_2.
  rename t' into t_final.
  rename t2 into t_mid_1.
  rename t1' into t2.
  rename t0 into t1'.
  assert (typ_pair t1 t1' <> typ_pair t2 t2') as fneq.
  unfold not; intro feq. rewrite <- feq in H2. contradiction.
(*   pose proof (coercion_FunTrans _ _ _ _ _ _ _ _ _ _ H2 D2_1 D2_2 D2_3) as D2. *)
  assert (coercion sigma (typ_pair t2 t2'::pi) AltNoSub (typ_pair t2 t2') RelPrim t_final C') as alreadyUsedSubtyping.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates no_pair_fun)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_pair_to_fun XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun T1 T3::pi) (typ_pair t2 t2'::pi) T1 T3 t2 t2' AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates to_uniquepair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cpair_to_pair XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_pair t2 t2'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_pair t2 t2' <> typ_pair T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_pair t2 t2'::pi) AltNoSub RelPrim (typ_pair t2 t2')) as forcontra.
          destruct (WF_p_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cpair_to_pair forcontra).
          unfold id in E1_neq. contradiction.
  destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1_2) as [D1_prim | [D1_fun | D1_pair]].
  SSCase "D1_prim ... D1 is level1".
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim  t_final (compose (typ_pair t1 t1') C (exp_base f))) as D1_Contra.
    eapply coercion_PrimTrans; eauto.
  unfold no_unnecessary_pair_subtyping_path, coerciongen in No_un_f.
    pose proof (No_un_p _ _ _ _ _ _ _ _ H D1_Contra (coercion_Id _ _ _ _ _) t2 t2' fneq) as from_Noun.
    assert ((exists C1, coercion sigma [typ_pair t2 t2'] AltSub (typ_pair t2 t2') RelPrim t_final C1) /\
            (exists C2 : exp,  coercion sigma [typ_pair t1 t1'] AltSub 
                    (typ_pair t1 t1') RelSub (typ_pair t2 t2') C2)) as forContra.
  split.
     SSSCase "Assertion Conj left".
     exists C'.
         eapply coercion_pi_strengthening.
         eapply relprim_sub_alt_ix.
         eapply alreadyUsedSubtyping.
         eauto using insingleton, in_eq.
     SSSCase "Assertion Conj right".
     exists (compose (typ_pair t1 t1') (id (typ_pair t2 t2')) (paircompose t1 t1' C1 C2)).
     eapply coercion_PairTrans.
     SSSSCase "Premise not in". 
     unfold not. intros.
       destruct (in_inv H3) as [fEq | inNil]. 
       rewrite fEq in fneq. eapply fneq. reflexivity.
       contradiction.
     SSSSCase "Premise Farg".
       auto.
     SSSSCase "Premise Fret".
       auto.
     SSSSCase "Streak right".
       unfold id. eapply coercion_Id. 
  contradiction.
  SSCase "D1_2_R ... D1 is fun sub".
  destruct D1_fun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D1_2_R_pair_to_fun [D1_2_R_PairSub D1_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim (typ_fun T1 T2) (compose (typ_pair t1 t1') B1 (exp_base f))) as pair_to_fun.
    eauto using coercion_PrimTrans, in_eq.
  unfold WF_no_fun_pair in WF_no_fp.
  destruct (WF_no_fp [typ_fun T1 T2] pi T1 T2 t1 t1' a B1 (compose (typ_pair t1 t1') B1 (exp_base f)) (in_eq _ _) H).
  contradiction.  
  SSCase "D1_2_R ... D1 is pair sub".
  destruct D1_pair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D1_2_R_Pfx [D1_2_R_PairSub D1_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim (typ_pair T1 T2) (compose (typ_pair t1 t1') B1 (exp_base f))) as D1_Contra.
   SSSCase "Assertion D1_Contra".
    eapply coercion_PrimTrans; eauto.
   assert (typ_pair t1 t1' <> typ_pair T1 T2) as Tpair_ineq.
    SSSCase "Assertion Tpair_ineq".
     eapply nonidentity_implies_inequality; eauto.
       unfold compose, id. discriminate.
   assert (coercion sigma pi a (typ_pair t1 t1') RelPrim (typ_pair t1 t1') (exp_lam (typ_pair t1 t1') (exp_bvar 0))) as D1_Contra_2.
     eapply coercion_Id;eauto. 
  unfold WF_to_uniquepair in WF_p_1.
  assert (typ_pair t1 t1' = typ_pair T1 T2) as Contra.
    destruct (WF_p_1 _ _ _ _ _ _ _ _ _ H D1_Contra_2 D1_Contra) as [A1 [A2 A3]].
    subst. auto.
  contradiction.
Case "D1 is FunTrans".
intros.
remember (typ_fun t1 t2) as tinitial.
remember RelSub as rs.
induction D2.
 SCase "D2 is C-Id (Symmetric)". 
  destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ H) D1_3) as [Eq1 Eq2].
  rewrite <- Eq1 in H. 
  contradiction.
 SCase "D2 is PrimTrans (Symmetric)".
  rename D2 into D2_2.
  clear IHD1_1 IHD1_2 IHD1_3 IHD2.
  rename t4 into t_final.
  rename t3 into t_mid_2.
  rename t1' into temp.
  rename t2 into t1'.
  rename temp into t2.
  subst t0.
  subst r.
  assert (typ_fun t1 t1' <> typ_fun t2 t2') as fneq.
  unfold not; intro feq. rewrite <- feq in H0. contradiction.
  assert (coercion sigma (typ_fun t2 t2'::pi) AltNoSub (typ_fun t2 t2') RelPrim t_final C') as alreadyUsedSubtyping.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates to_uniquefunc)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_fun t2 t2'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_fun t2 t2' <> typ_fun T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_fun t2 t2'::pi) AltNoSub RelPrim (typ_fun t2 t2')) as forcontra.
          destruct (WF_f_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates no_fun_pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun t2 t2'::pi) (typ_pair T1 T3::pi) t2 t2' T1 T3 AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.
  pose proof (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2_2) as D2_2_LR.
  destruct D2_2_LR as [D2_2_prim | [D2_2_fun | D2_2_pair]].
  SSCase "D2_2_prim ... D2 is level1".
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim t_final (compose (typ_fun t1 t1') C (exp_base f))) as D2_Contra.
    eapply coercion_PrimTrans; eauto.
  unfold no_unnecessary_fun_subtyping_path, coerciongen in No_un_f.
    pose proof (No_un_f _ _ _ _ _ _ _ _ H D2_Contra (coercion_Id _ _ _ _ _) t2 t2' fneq) as from_Noun.
    assert ((exists C1, coercion sigma [typ_fun t2 t2'] AltSub (typ_fun t2 t2') RelPrim t_final C1) /\
            (exists C2 : exp,  coercion sigma [typ_fun t1 t1'] AltSub
                    (typ_fun t1 t1') RelSub (typ_fun t2 t2') C2)) as forContra.
  split.
     SSSCase "Assertion Conj left".
     exists C'.
        eapply coercion_pi_strengthening.
        eapply relprim_sub_alt_ix.
        apply alreadyUsedSubtyping.
        eauto using insingleton, in_eq.
     SSSCase "Assertion Conj right".
     exists (compose (typ_fun t1 t1') (id (typ_fun t2 t2')) (funcompose (typ_fun t1 t1') t2 C1 C2)).
     eapply coercion_FunTrans.
       SSSSCase "Premise not in". 
       unfold not. intros.
         destruct (in_inv H3) as [fEq | inNil]. 
         rewrite fEq in fneq. eapply fneq. reflexivity.
         contradiction.
       SSSSCase "Premise Farg".
         auto.
       SSSSCase "Premise Fret".
         auto.
       SSSSCase "Streak right".
         unfold id. eapply coercion_Id. 
  contradiction.
  SSCase "D1_2_fun ... D2 is level 2".
  destruct D2_2_fun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D2_2_R_Pfx [D2_2_R_FunSub D2_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim (typ_fun T1 T2) (compose (typ_fun t1 t1') B1 (exp_base f))) as D2_Contra.
   SSSCase "Assertion D1_Contra".
    eapply coercion_PrimTrans; eauto.
  assert (typ_fun t1 t1' <> typ_fun T1 T2) as Tfun_ineq.
   SSSCase "Assertion Tfun_ineq".
   eapply nonidentity_implies_inequality; eauto.
     unfold compose, id. discriminate.
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim (typ_fun t1 t1') (exp_lam (typ_fun t1 t1') (exp_bvar 0))) as D2_Contra_2.
    eapply coercion_Id;eauto.
  unfold WF_to_uniquefunc in WF_f_1.
  assert (typ_fun t1 t1' = typ_fun T1 T2) as Contra.
    destruct (WF_f_1 _ _ _ _ _ _ _ _ _ H D2_Contra_2 D2_Contra) as [A1 [A2 A3]].
    subst. auto.
  contradiction.

  SSCase "D2_2_R ... D2 is pair sub".
  destruct D2_2_pair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D1_2_R_fun_to_pair [D1_2_R_PairSub D1_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_fun t1 t1') RelPrim (typ_pair T1 T2) (compose (typ_fun t1 t1') B1 (exp_base f))) as fun_to_pair.
    eauto using coercion_PrimTrans, in_eq.
  unfold WF_no_fun_pair in WF_no_fp.
  destruct (WF_no_fp  pi [typ_pair T1 T2] t1 t1' T1 T2 a (compose (typ_fun t1 t1') B1 (exp_base f)) B1 H (in_eq _ _)).
  contradiction.  

 SCase "D2 is FunTrans".
  rename t' into t_final.
  injection Heqtinitial. intros. subst t0. subst t3. clear Heqtinitial.
  rename t1' into s1.
  rename t2' into s1'.
  rename t1'0 into s2.
  rename t2'0 into s2'.
  rename t2 into t1'.
  rename C' into C_Sfx_1.
  rename C'0 into C_Sfx_2.


  assert (coercion sigma (typ_fun s1 s1'::pi) AltNoSub (typ_fun s1 s1') RelPrim t_final C_Sfx_1) as alreadyUsedSubtyping1.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates to_uniquefunc)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_fun s1 s1'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_fun s1 s1' <> typ_fun T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_fun s1 s1'::pi) AltNoSub RelPrim (typ_fun s1 s1')) as forcontra.
          destruct (WF_f_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates no_fun_pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun s1 s1'::pi) (typ_pair T1 T3::pi) s1 s1' T1 T3 AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.


  assert (coercion sigma (typ_fun s2 s2'::pi) AltNoSub (typ_fun s2 s2') RelPrim t_final C_Sfx_2) as alreadyUsedSubtyping2.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates to_uniquefunc)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_fun s2 s2'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_fun s2 s2' <> typ_fun T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_fun s2 s2'::pi) AltNoSub RelPrim (typ_fun s2 s2')) as forcontra.
          destruct (WF_f_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates no_fun_pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun s2 s2'::pi) (typ_pair T1 T3::pi) s2 s2' T1 T3 AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.

  assert (typ_fun s1 s1' = typ_fun s2 s2') as fun_eq.
    unfold no_multiple_fun_subtyping_paths, coerciongen in No_mul_f.
    eapply (No_mul_f t_final).
      eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply alreadyUsedSubtyping1. eauto using insingleton, in_eq.
      eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply alreadyUsedSubtyping2. eauto using insingleton, in_eq.
    eapply coercion_pi_strengthening.
      eapply coercion_FunTrans.
        apply H0.
        apply D1_1. apply D1_2. eapply coercion_Id. eauto using insingleton, in_eq.
    eapply coercion_pi_strengthening.
      eapply coercion_FunTrans.
        apply H1.
        apply D2_1. apply D2_2. eapply coercion_Id. eauto using insingleton, in_eq.
  injection fun_eq; intros; subst s2; subst s2'. clear fun_eq.
  assert (C_Sfx_1 = C_Sfx_2) as sfx_eq.
    unfold WF_uniquepath in WF_up_1.
    eapply (WF_up_1 _ _ _ _ _ (typ_fun s1 s1'::pi) (in_eq _ _) alreadyUsedSubtyping1 alreadyUsedSubtyping2).
  subst C_Sfx_2.
  clear IHD2_1 IHD2_2 IHD2_3 IHD1_3.
  assert (C1 = C0) as eq_10.
    eapply IHD1_1; eauto using in_eq.
  assert (C2 = C3) as eq_23.
    eapply IHD1_2; eauto using in_eq.
  subst C0. subst C3. auto.

 SCase "D2 is PairTrans".
 subst. discriminate.

Case "D1 is PairTrans".
intros.
remember (typ_pair t1 t2) as tinitial.
remember RelSub as rs.
induction D2.
 SCase "D2 is C-Id (Symmetric)". 
  destruct (cycles_are_identity _ _ _ _ _ _ _ (in_cons _ _ _ H) D1_3) as [Eq1 Eq2].
  rewrite <- Eq1 in H. 
  contradiction.
 SCase "D2 is PrimTrans (Symmetric)".
  rename D2 into D2_2.
  clear IHD1_1 IHD1_2 IHD1_3 IHD2.
  rename t4 into t_final.
  rename t3 into t_mid_2.
  rename t1' into temp.
  rename t2 into t1'.
  rename temp into t2.
  subst t0.
  subst r.
  assert (typ_pair t1 t1' <> typ_pair t2 t2') as fneq.
  unfold not; intro feq. rewrite <- feq in H0. contradiction.
  assert (coercion sigma (typ_pair t2 t2'::pi) AltNoSub (typ_pair t2 t2') RelPrim t_final C') as alreadyUsedSubtyping.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates no fun pair)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun T1 T3::pi) (typ_pair t2 t2'::pi) T1 T3 t2 t2' AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates unique_pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_pair t2 t2'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_pair t2 t2' <> typ_pair T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_pair t2 t2'::pi) AltNoSub RelPrim (typ_pair t2 t2')) as forcontra.
          destruct (WF_p_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
  pose proof (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2_2) as D2_2_LR.
  destruct D2_2_LR as [D2_2_prim | [D2_2_fun | D2_2_pair]].
  SSCase "D2_2_prim ... D2 is level1".
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim t_final (compose (typ_pair t1 t1') C (exp_base f))) as D2_Contra.
    eapply coercion_PrimTrans; eauto.
  unfold no_unnecessary_pair_subtyping_path, coerciongen in No_un_p.
    pose proof (No_un_p _ _ _ _ _ _ _ _ H D2_Contra (coercion_Id _ _ _ _ _) t2 t2' fneq) as from_Noun.
    assert ((exists C1, coercion sigma [typ_pair t2 t2'] AltSub (typ_pair t2 t2') RelPrim t_final C1) /\
            (exists C2 : exp,  coercion sigma [typ_pair t1 t1'] AltSub
                    (typ_pair t1 t1') RelSub (typ_pair t2 t2') C2)) as forContra.
  split.
     SSSCase "Assertion Conj left".
     exists C'.         
         eapply coercion_pi_strengthening. eapply relprim_sub_alt_ix. apply alreadyUsedSubtyping. eauto using insingleton, in_eq.
     SSSCase "Assertion Conj right".
     exists (compose (typ_pair t1 t1') (id (typ_pair t2 t2')) (paircompose  t1 t1' C1 C2)).
     eapply coercion_PairTrans.
       SSSSCase "Premise not in". 
       unfold not. intros.
         destruct (in_inv H3) as [fEq | inNil]. 
         rewrite fEq in fneq. eapply fneq. reflexivity.
         contradiction.
       SSSSCase "Premise Farg".
         auto.
       SSSSCase "Premise Fret".
         auto.
       SSSSCase "Streak right".
         unfold id. eapply coercion_Id. 
  contradiction.
  SSCase "D1_2_fun ... D2 is level 2".
  destruct D2_2_fun as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D1_2_R_fun_to_pair [D1_2_R_PairSub D1_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim (typ_fun T1 T2) (compose (typ_pair t1 t1') B1 (exp_base f))) as fun_to_pair.
    eauto using coercion_PrimTrans, in_eq.
  unfold WF_no_fun_pair in WF_no_fp.
  destruct (WF_no_fp [typ_fun T1 T2] pi T1 T2 t1 t1'  a B1 (compose (typ_pair t1 t1') B1 (exp_base f)) (in_eq _ _) H).
  contradiction.  
  SSCase "D2_2_R ... D2 is pair sub".
  destruct D2_2_pair as [T1 [T2 [S1 [S2 [B1 [B2 [B3 [theta' [D1_2_Ineq [InTheta' [alt_imp [D2_2_R_Pfx [D2_2_R_PairSub D2_2_R_Sfx]]]]]]]]]]]]].
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim (typ_pair T1 T2) (compose (typ_pair t1 t1') B1 (exp_base f))) as D2_Contra.
   SSSCase "Assertion D1_Contra".
    eapply coercion_PrimTrans; eauto.
  assert (typ_pair t1 t1' <> typ_pair T1 T2) as Tfun_ineq.
   SSSCase "Assertion Tfun_ineq".
   eapply nonidentity_implies_inequality; eauto.
     unfold compose, id. discriminate.
  assert (coercion sigma pi a (typ_pair t1 t1') RelPrim (typ_pair t1 t1') (exp_lam (typ_pair t1 t1') (exp_bvar 0))) as D2_Contra_2.
    eapply coercion_Id;eauto.
  unfold WF_to_uniquepair in WF_p_1.
  assert (typ_pair t1 t1' = typ_pair T1 T2) as Contra.
    destruct (WF_p_1 _ _ _ _ _ _ _ _ _ H D2_Contra_2 D2_Contra) as [A1 [A2 A3]].
    subst. auto.
  contradiction.

 SCase "D2 is FunTrans".
subst. discriminate.

SCase "D2 is PairTrans".
  rename t' into t_final.
  injection Heqtinitial. intros. subst t0. subst t3. clear Heqtinitial.
  rename t1' into s1.
  rename t2' into s1'.
  rename t1'0 into s2.
  rename t2'0 into s2'.
  rename t2 into t1'.
  rename C' into C_Sfx_1.
  rename C'0 into C_Sfx_2.

  assert (coercion sigma (typ_pair s1 s1'::pi) AltNoSub (typ_pair s1 s1') RelPrim t_final C_Sfx_1) as alreadyUsedSubtyping1.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D1_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
        auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates no_fp)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun T1 T3::pi) (typ_pair s1 s1'::pi) T1 T3 s1 s1' AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates to unique pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_pair s1 s1'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_pair s1 s1' <> typ_pair T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_pair s1 s1'::pi) AltNoSub RelPrim (typ_pair s1 s1')) as forcontra.
          destruct (WF_p_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
  assert (coercion sigma (typ_pair s2 s2'::pi) AltNoSub (typ_pair s2 s2') RelPrim t_final C_Sfx_2) as alreadyUsedSubtyping2.
    destruct (relsub_derivations_use_subtyping_atmost_once _ _ _ _ _ _ WF_f_1 WF_p_1 WF_no_fp (in_eq _ _) D2_3) as [D2_3_prim | [D2_3_fun | D2_3_pair]].
      SSCase "Assertion: D2_3 prim".
       auto.
      SSCase "Assertoin: D2_3 is funsub (impos violates no_fp)".
        destruct D2_3_fun as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_fun_to_pair XX]]]]]]]]]]]].
        unfold WF_no_fun_pair in WF_no_fp.
        destruct (WF_no_fp  (typ_fun T1 T3::pi) (typ_pair s2 s2'::pi) T1 T3 s2 s2' AltNoSub E1 E1 (in_eq _ _) (in_eq _ _)).
        contradiction.
      SSCase "Assertion: D2_3 is pair sub (violates to unique pair)".
        destruct D2_3_pair as [T1 [T3 [S1 [S2 [E1 [E2 [E3 [theta'' [tneq [notintheta'' [alt_imp [cfun_to_fun XX]]]]]]]]]]]].
        assert (E1 <> (id (typ_pair s2 s2'))) as E1_neq.
          unfold not; intro. subst E1. pose proof (alt_imp (refl_equal _)). discriminate.
          assert (typ_pair s2 s2' <> typ_pair T1 T3).
            eauto using nonidentity_implies_inequality, in_eq.
          pose proof (coercion_Id sigma (typ_pair s2 s2'::pi) AltNoSub RelPrim (typ_pair s2 s2')) as forcontra.
          destruct (WF_p_1  _ _ _ _ _ _ _ _ _ (in_eq _ _) cfun_to_fun forcontra).
          unfold id in E1_neq. contradiction.
  assert (typ_pair s1 s1' = typ_pair s2 s2') as fun_eq.
    unfold no_multiple_pair_subtyping_paths, coerciongen in No_mul_p.
    eapply (No_mul_p t_final t1 t1' s1 s1' s2 s2' C_Sfx_1 C_Sfx_2).
     eapply coercion_pi_strengthening.
        eapply relprim_sub_alt_ix. apply alreadyUsedSubtyping1. eauto using insingleton, in_eq.
     eapply coercion_pi_strengthening.
        eapply relprim_sub_alt_ix. apply alreadyUsedSubtyping2. eauto using insingleton, in_eq.
    eapply coercion_pi_strengthening.
      eapply coercion_PairTrans.
        apply H0.
        apply D1_1. apply D1_2. eapply coercion_Id. eauto using insingleton, in_eq.
    eapply coercion_pi_strengthening.
      eapply coercion_PairTrans.
        apply H1.
        apply D2_1. apply D2_2. eapply coercion_Id. eauto using insingleton, in_eq.
  injection fun_eq; intros; subst s2; subst s2'. clear fun_eq.
  assert (C_Sfx_1 = C_Sfx_2) as sfx_eq.
    unfold WF_uniquepath in WF_up_1.
    eapply (WF_up_1 _ _ _ _ _ (typ_pair s1 s1'::pi) (in_eq _ _) alreadyUsedSubtyping1 alreadyUsedSubtyping2).
  subst C_Sfx_2.
  clear IHD2_1 IHD2_2 IHD2_3 IHD1_3.
  assert (C1 = C0) as eq_10.
    eapply IHD1_1; eauto using in_eq.
  assert (C2 = C3) as eq_23.
    eapply IHD1_2; eauto using in_eq.
  subst C0. subst C3. auto.
Qed.
   
