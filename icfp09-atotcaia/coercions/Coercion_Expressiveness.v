Require Export Coercion_Subty.
Require Import Classical.

Hint Constructors coercion.
Hint Resolve in_eq in_cons in_inv in_nil.
Hint Resolve coercion_pi_strengthening.
Hint Resolve insingleton.
Hint Resolve sub_alt_ix.
Hint Unfold not.
Hint Unfold coerciongen id.
Hint Resolve in_ext in_not_in not_in_singleton.
Hint Constructors nd_typing subty.

Inductive typing_subty : Sigma -> Gamma -> exp -> typ -> Prop :=
| typing_subty_Var :
  forall sigma G x t, 
    (binds x t G) -> 
    (typing_subty sigma G (exp_fvar x) t)

| typing_subty_Sub :
  forall sigma G e t t', 
    (typing_subty sigma G e t) -> 
    (subty sigma t t') -> 
    (typing_subty sigma G e t') 
    
| typing_subty_Abs : 
  forall L sigma G tx t e, 
    (forall x, x `notin` L -> 
      (typing_subty sigma ([(x,tx)] ++ G) (open_exp 0 (exp_fvar x) e) t)) -> 
    (typing_subty sigma G (exp_lam tx e) (typ_fun tx t))
    
| typing_subty_Pair : 
  forall sigma G e1 e2 t1 t2,
    (typing_subty sigma G e1 t1) -> 
    (typing_subty sigma G e2 t2) -> 
    (typing_subty sigma G (exp_pair e1 e2) (typ_pair t1 t2))
    
| typing_subty_App :
  forall sigma G e1 t t' e2,
    (typing_subty sigma G e1 (typ_fun t' t)) -> 
    (typing_subty sigma G e2 t') -> 
    (typing_subty sigma G (exp_app e1 e2) t)

| typing_subty_Proj_1 :
  forall sigma G e t1 t2, 
    (typing_subty sigma G e (typ_pair t1 t2)) -> 
    (typing_subty sigma G (exp_proj One e) t1)

| typing_subty_Proj_2 :
  forall sigma G e t1 t2, 
    (typing_subty sigma G e (typ_pair t1 t2)) -> 
    (typing_subty sigma G (exp_proj Two e) t2)
.
 

Lemma subty_fun_shape : forall sigma t t1 t2, 
  WF_subty sigma -> 
  subty sigma t (typ_fun t1 t2) -> 
  (exists s1, exists s2, t = (typ_fun s1 s2) /\
    (subty sigma t1 s1) /\ (subty sigma s2 t2)).
Proof.
intros until 1. rename H into WF. intro S.
remember (typ_fun t1 t2) as t12.
generalize dependent t1.
generalize dependent t2.
induction S.
Case "Id". intros.
subst.
exists t1. exists t2. eauto using Subty_Id.
Case "Base". intros. 
subst.
unfold WF_subty in WF.
destruct(WF _ _ H) as [s1 [s2 contra]].
discriminate contra.
Case "Trans". intros. subst.
destruct (IHS2 WF _ _ (refl_equal _)) as [s1 [s2 [t0_eq [Sub1 Sub2]]]].
subst.
destruct (IHS1 WF _ _ (refl_equal _)) as [r1 [r2 [t_eq [SubR1 SubR2]]]].
subst.
exists r1. exists r2.
intuition; eauto using Subty_Trans.
Case "Fun".
intros. subst. injection Heqt12; intros; subst.
exists t1. exists t2. intuition;eauto.
Case "Pair".
intros. discriminate.
Qed.

Lemma subty_pair_shape : forall sigma t t1 t2, 
  WF_subty sigma -> 
  subty sigma t (typ_pair t1 t2) -> 
  (exists s1, exists s2, t = (typ_pair s1 s2) /\
    (subty sigma s1 t1) /\ (subty sigma s2 t2)).
Proof.
intros until 1. rename H into WF. intro S.
remember (typ_pair t1 t2) as t12.
generalize dependent t1.
generalize dependent t2.
induction S.
Case "Id". intros.
subst.
exists t1. exists t2. eauto using Subty_Id.
Case "Base". intros. 
subst.
unfold WF_subty in WF.
destruct(WF _ _ H) as [s1 [s2 contra]].
discriminate contra.
Case "Trans". intros. subst.
destruct (IHS2 WF _ _ (refl_equal _)) as [s1 [s2 [t0_eq [Sub1 Sub2]]]].
subst.
destruct (IHS1 WF _ _ (refl_equal _)) as [r1 [r2 [t_eq [SubR1 SubR2]]]].
subst.
exists r1. exists r2.
intuition; eauto using Subty_Trans.
Case "Fun".
intros. discriminate.
Case "Pair".
intros. subst. injection Heqt12; intros; subst.
exists t1. exists t2. intuition;eauto.
Qed.

Fixpoint sub (x:atom) (y:atom) (e:exp) {struct e} : exp :=
  match e with
    | exp_fvar z => if x==z then exp_fvar y else exp_fvar z
    | exp_bvar i => exp_bvar i
    | exp_base b => exp_base b
    | exp_app e1 e2 => exp_app (sub x y e1) (sub x y e2)
    | exp_pair e1 e2 => exp_pair (sub x y e1) (sub x y e2)
    | exp_proj a e1 => exp_proj a (sub x y e1)
    | exp_cast e t => exp_cast (sub x y e) t
    | exp_lam t e => exp_lam t (sub x y e)
  end.

Lemma subst_open : forall e x y n fvs,
  freevars e fvs -> x `notin` fvs -> 
  (sub x y (open_exp n (exp_fvar x) e)) = (open_exp n (exp_fvar y) e).
intros.
generalize dependent n.
generalize dependent fvs.
induction e; try solve [intros; simpl; inversion H; subst; f_equal; firstorder].
   intros. simpl. destruct (n0===n). simpl. destruct (x==x) as [AA | BB]; eauto || destruct BB;eauto. simpl. eauto.
   intros. simpl. destruct (x==a). subst. inversion H. subst. fsetdec. eauto.
Qed.


Lemma sub_open_commute : forall x y z e n,
  x <> z -> 
  ((sub x y (open_exp n (exp_fvar z) e)) =
    (open_exp n (exp_fvar z) (sub x y e))). 
Proof.
 intros x y z e n x_neq_z.
 generalize dependent n.
 induction e; try solve [intros; simpl; f_equal; eauto].
 Case "exp_bvar".
   intros. simpl. destruct (n0===n). simpl. destruct (x==z); simpl; intuition.
   simpl. eauto.
 Case "exp_fvar".
   intros. simpl. destruct (x==a); simpl; eauto.
Qed.

Hint Unfold compose funcompose paircompose.

Lemma coercions_are_closed: forall sigma d pi t t' m a, 
  (coercion sigma pi a t d t' m) -> (forall x y, sub x y m = m).
intros. rename H into C.
induction C; 
 simpl. eauto.
 unfold compose. simpl. rewrite IHC. eauto.
 unfold compose. unfold funcompose. simpl. rewrite IHC1. rewrite IHC2. rewrite IHC3. eauto.
 unfold compose. unfold paircompose. simpl. rewrite IHC1. rewrite IHC2. rewrite IHC3. eauto.
Qed.


Lemma sub_coerce_commute : forall sigma d t t' m e x y, 
  (coerciongen sigma t d t' m) -> 
  (sub x y (coerce m e)) = (coerce m (sub x y e)).
Proof.
intros.
unfold coerciongen in H.
destruct (classic (exists t, m = id t)) as [[t0 m_eq] | not_ex].
subst. simpl. eauto.
pose proof (not_ex_all_not _ _ not_ex).
simpl in H0.
rewrite (coerce_non_identity _ e H0).
rewrite (coerce_non_identity _ (sub x y e) H0).
simpl.
rewrite (coercions_are_closed _ _ _ _ _ _ _ H x y). eauto.
Qed.


Lemma name_subst : forall sigma G gamma gamma' x tx e e' t d d', 
  ok sigma -> ok G -> (G = (gamma'++[(x,tx)]++gamma)) ->
  (nd_typing sigma G d d' e e' t) -> 
  (forall y, (ok (gamma'++[(y,tx)]++gamma)) ->
    (nd_typing sigma (gamma'++[(y,tx)]++gamma) d d' (sub x y e) (sub x y e') t)).
intros until 1. rename H into ok_S. intros okG Geq T.
generalize dependent gamma'.
induction T; try solve [intros; simpl sub; f_equal; eauto using sub_coerce_commute].
Case "exp_fvar".
intros.  simpl sub. destruct (x==x0). 
  SCase "x = x0".
    subst.
    assert (tx=t); eauto using binds_id. subst.
    eapply nd_typing_Var. eauto using binds_mid.
  SCase "x <> x0".
    eapply nd_typing_Var.
    subst G.
    destruct (binds_concat_inv _ _ _ _ _ H) as [bTL | bHD].
       SSCase "binds x0 gamma".
        destruct bTL as [notin_hd b_tail].
        destruct (binds_concat_inv _ _ _ _ _ b_tail) as [[ig binds_x0_g] | bhd]; eauto using binds_tail, binds_singleton_inv; intuition.
        SSSCase "x=x0, impos".
             destruct (binds_singleton_inv _ _ _ _ _ bhd). subst; intuition.
       SSCase "binds x0 gamma'". eauto.
Case "exp_lam".
intros. simpl sub.
eapply (nd_typing_Abs (dom G `union` L `union` singleton y `union` singleton x `union` dom (gamma' ++ [(y,tx)] ++ gamma))). intros.
assert (ok ([(x0, t_x)]++G)). eauto.
assert (x0 `notin` L). eauto.
assert (x0 `notin` singleton x) as x0_notin_x. fsetdec.
assert (x <> x0) as x0_neq_x. fsetdec.
rewrite <- (sub_open_commute x y x0 e 0 x0_neq_x).
rewrite <- (sub_open_commute x y x0 e' 0 x0_neq_x).
rewrite_env (([(x0, t_x)] ++ gamma') ++ [(y, tx)] ++ gamma).
eapply H0. fsetdec. eauto. eauto. 
subst G. 
rewrite_env (([(x0, t_x)] ++ gamma') ++ [(x, tx)] ++ gamma).
eauto.
simpl.
rewrite_env ((gamma' ++ [(y, tx)] ++ gamma)).
eapply ok_cons. eauto. fsetdec.
Case "exp_app".
intros. simpl sub.
rewrite (sub_coerce_commute _ _ _ _ m1 e1' x y H).
rewrite (sub_coerce_commute _ _ _ _ m2 e2' x y H0).
eauto.
Case "exp_proj one".
intros. simpl sub.
rewrite (sub_coerce_commute _ _ _ _ m e' x y H).
eauto.
Case "exp_proj two".
intros. simpl sub.
rewrite (sub_coerce_commute _ _ _ _ m e' x y H).
eauto.
Qed.


Theorem expressiveness : forall sigma gamma e t, 
  ok sigma -> ok gamma -> WF_subty sigma -> 
  (typing_subty sigma gamma e t) -> 
  (exists e', exists t', 
    (nd_typing sigma gamma RelPrim RelSub e e' t') /\ subty sigma t' t).
Proof.
intros sigma gamma e t okS okG WF T.
induction T.
Case "Var".
 exists (exp_fvar x). exists t. intuition.
Case "Sub".
 destruct (IHT okS okG WF) as [E [s [Typing S]]].
 exists E. exists s. intuition; eauto.
Case "Abs".
 destruct (freevars_totality e) as [fvs fvse].
 pick fresh y.
 assert (y `notin` L) as ynotinL.
   fsetdec.
 assert (ok ([(y,tx)]++G)) as ok_yG.
   rewrite_env ((y,tx)::G).
   eapply ok_cons; [eauto | fsetdec].
 destruct (H0 y ynotinL okS ok_yG WF) as [E [s [Typing S]]].
 assert (y `notin` fvs) as y_notin_fvs. fsetdec.
(*  destruct (name_irrelevance _ _ _ _ _ _ _ _ okS ok_yG fvse y_notin_fvs Typing) as [ebody forall_ebody]. *)
 destruct (open_inverse_nd _ _ _ _ _ _ _ _ _ okS ok_yG Typing) as [E' [E'_eq fvsE']].
 exists (exp_lam tx E').
 exists (typ_fun tx s).
 split.
 SCase "typing".
   eapply (nd_typing_Abs (dom G)).
   intros.
   assert (y `notin` fvs) as ynotinfvs; eauto.
   destruct (freevars_totality E') as [fvse' freevarsE'].
   rewrite <- (subst_open e y x 0 _ fvse ynotinfvs).
   rewrite <- (subst_open E' y x 0 _ freevarsE' (fvsE' _ freevarsE')).
   rewrite_env (nil++[(x,tx)]++G).
   eapply name_subst. eauto. eauto. eauto. eauto. subst. eauto. 
   rewrite_env ([(x,tx)]++G). eauto.
 SCase "subty". auto.
Case "Pair".
   intuition.
   destruct H0 as [E1 [S1 [Typing1 Sub_1]]].
   destruct H1 as [E2 [S2 [Typing2 Sub_2]]].
   exists (exp_pair E1 E2).
   exists (typ_pair S1 S2).
   intuition; eauto.
Case "App".
  intuition.
  destruct H0 as [E1 [S1 [Typing1 Sub_1]]].
  destruct H1 as [E2 [S2 [Typing2 Sub_2]]].
  destruct (subty_fun_shape _ _ _ _ WF Sub_1) as [S1_a [S1_r [S1_eq [Sub_arg Sub_ret]]]].
  subst S1.
  assert (subty sigma S2 S1_a) as sub_RHS.
    eauto.
  destruct (subty_coercion _ _ _ WF sub_RHS) as [m_RHS D_RHS].
  exists (exp_app E1 (coerce m_RHS E2)).
  exists S1_r.
  split.
  SCase "Typing".
     assert ((coerce (id (typ_fun S1_a S1_r)) E1) = E1) as E1_c. unfold coerce, id. simpl. eauto.
     rewrite <- E1_c.
     eapply nd_typing_App. eapply Typing1. eapply Typing2.
     unfold coerciongen. unfold id. apply coercion_Id.
     unfold coerciongen. eauto. 
  SCase "Subty ".
   eauto.
Case "Proj one".
   intuition.  
   destruct H as [EPair [SPair [Typing Sub]]].
   destruct (subty_pair_shape _ _ _ _ WF Sub) as [S1 [S2 [SPair_eq [Sub_fst Sub_snd]]]].
   subst SPair.
   exists (exp_proj One (coerce (id (typ_pair S1 S2)) EPair)). unfold id.
   exists S1.
   split.
   SCase "Typing".
      eauto.
   SCase "Subty".
     eauto.
Case "Proj Two".
   intuition.  
   destruct H as [EPair [SPair [Typing Sub]]].
   destruct (subty_pair_shape _ _ _ _ WF Sub) as [S1 [S2 [SPair_eq [Sub_fst Sub_snd]]]].
   subst SPair.
   exists (exp_proj Two (coerce (id (typ_pair S1 S2)) EPair)). unfold id.
   exists S2.
   split.
   SCase "Typing".
      eauto.
   SCase "Subty".
     eauto.
Qed.


