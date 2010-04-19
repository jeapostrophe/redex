Require Export Coercion_Infrastructure.

Hint Constructors coercion.
Hint Resolve in_eq in_cons in_inv in_nil.
Hint Resolve insingleton.
Hint Unfold not.
Hint Unfold coerciongen id.
Hint Resolve in_not_in not_in_singleton.
Hint Constructors nd_typing.

Inductive typing_std : Gamma -> exp -> typ -> Prop :=
| typing_std_Var :
  forall G x t, 
    (binds x t G) -> 
    (typing_std G (exp_fvar x) t)

| typing_std_Base :
  forall G x t, 
    (binds x t G) -> 
    (typing_std G (exp_base x) t)
    
| typing_std_Abs : 
  forall L G tx t e, 
    (forall x, x `notin` L -> 
      (typing_std ([(x,tx)] ++ G) (open_exp 0 (exp_fvar x) e) t)) -> 
    (typing_std G (exp_lam tx e) (typ_fun tx t))
    
| typing_std_Pair : 
  forall G e1 e2 t1 t2,
    (typing_std G e1 t1) -> 
    (typing_std G e2 t2) -> 
    (typing_std G (exp_pair e1 e2) (typ_pair t1 t2))
    
| typing_std_App :
  forall G e1 t t' e2,
    (typing_std G e1 (typ_fun t' t)) -> 
    (typing_std G e2 t') -> 
    (typing_std G (exp_app e1 e2) t)

| typing_std_Proj_1 :
  forall G e t1 t2, 
    (typing_std G e (typ_pair t1 t2)) -> 
    (typing_std G (exp_proj One e) t1)

| typing_std_Proj_2 :
  forall G e t1 t2, 
    (typing_std G e (typ_pair t1 t2)) -> 
    (typing_std G (exp_proj Two e) t2)
.

Hint Constructors typing_std.

Lemma typing_std_weakening: forall gamma gamma' e t x tx,
  ok (gamma' ++ gamma) -> 
  typing_std (gamma' ++ gamma) e t -> 
  ok (gamma' ++ [(x, tx)] ++ gamma) -> 
  typing_std (gamma' ++ [(x,tx)] ++ gamma) e t.
intros gamma gamma' e t x tx ok_gg T ok_gxg.
remember (gamma' ++ gamma) as gg.
generalize dependent gamma'.
induction T; try solve [intros; subst; simpl; eauto]. 
Case "fvar".
intros. subst G.
destruct (binds_concat_inv _ _ _ _ _ H);
  eauto using binds_tail, binds_head, fresh_mid_tail. 
Case "base".
intros. subst G.
destruct (binds_concat_inv _ _ _ _ _ H);
  eauto using binds_tail, binds_head, fresh_mid_tail.
Case "lam".
 intros. subst.
 eapply (typing_std_Abs ((L `union` singleton x) `union` dom (gamma' ++ gamma))). 
 intros. rewrite_env (([(x0, tx0)] ++ gamma') ++ [(x, tx)] ++ gamma).
 eapply H0; try solve [eauto || fsetdec].
 rewrite_env ((x0, tx0)::(gamma' ++ [(x, tx)] ++ gamma)).
 eapply ok_cons. eauto. 
   rewrite (dom_concat _  ([(x,tx)] ++ gamma) gamma').
   rewrite (dom_concat _  gamma [(x,tx)]). simpl.
   rewrite (dom_concat _  gamma gamma') in H1. fsetdec.
Qed.


Lemma typing_std_weakening_list: forall gamma gamma' e t gamma'', 
  ok (gamma' ++ gamma) -> 
  typing_std (gamma' ++ gamma) e t -> 
  ok (gamma' ++ gamma'' ++ gamma) -> 
  typing_std (gamma' ++ gamma'' ++ gamma) e t.
Proof.
intros.
induction gamma''. simpl. eauto.
induction a. 
assert (ok (gamma' ++ gamma'' ++ gamma)). clear - H1.
rewrite_env (gamma' ++ [(a,b)] ++ (gamma'' ++ gamma)) in H1.
eauto using ok_remove_mid.
rewrite_env (gamma' ++ [(a,b)] ++ (gamma'' ++ gamma)).
eauto using typing_std_weakening.
Qed.

Lemma coercion_weakening : forall sigma sigma' pi d a t t' m, 
  (ok (sigma' ++ sigma)) -> 
  (coercion sigma pi a t d t' m) -> 
  (coercion (sigma' ++ sigma) pi a t d t' m).
intros.
induction H0; try solve [simpl; eauto using binds_tail].
Qed.

Hint Resolve typing_std_weakening. 

Lemma lc_open_noop : forall e x n, 
  (lc n e) -> 
  (open_exp n (exp_fvar x) e) = e.
Proof.
intros. generalize dependent n.
induction e; try solve [intros; inversion H; try unfold open_exp in *; subst; simpl; try rewrite (IHe _ H2); firstorder || eauto || omega].
Case "bvar".
intros.
 inversion H. subst. simpl. destruct (n0 === n). subst. assert False as f. omega. destruct f. eauto.
Case "app".
intros. inversion H. subst. simpl. rewrite (IHe1 _ H3). rewrite (IHe2 _ H4).  eauto.
Case "pair".
intros. inversion H. subst. simpl. rewrite (IHe1 _ H3). rewrite (IHe2 _ H4).  eauto.
Qed.

Lemma coercion_typing : forall sigma pi d a t t' m, 
  (ok sigma) -> 
  (coercion sigma pi a t d t' m) -> 
  (typing_std sigma m (typ_fun t t')).
Proof.
intros. rename H into ok_S. rename H0 into C.
induction C.
Case "id".
eapply (typing_std_Abs (dom sigma)). intros; simpl open_exp. eapply typing_std_Var. eauto.
Case "compose".
unfold compose. 
eapply (typing_std_Abs (dom sigma)). intros; simpl open_exp.
rewrite_env (nil ++ [(x,t1)] ++ sigma). 
eapply typing_std_App.
assert (lc 0 C); eauto using coercion_lc.
rewrite (lc_open_noop _ x _ H2). 
  eapply typing_std_weakening; eauto || simpl; eauto.
  eapply typing_std_App.
    eapply typing_std_weakening; eauto || simpl; eauto.
  eauto.
Case "funcompose".
unfold compose, funcompose in *. 
eapply (typing_std_Abs (dom sigma)).
intros.  simpl. 
rewrite_env (nil ++ [(x,(typ_fun t1 t2))] ++ sigma). 
eapply typing_std_App.
assert (lc 0 C') as lc_C'; eauto using coercion_lc.
rewrite (lc_open_noop _ x _ lc_C').
   eapply typing_std_weakening; eauto || simpl; eauto.
eapply typing_std_App.
eapply (typing_std_Abs (dom ([(x,typ_fun t1 t2)] ++ sigma))).
intros.  
simpl.
eapply (typing_std_Abs (dom ([(x0, typ_fun t1 t2)] ++ [(x,typ_fun t1 t2)] ++ sigma))).
intros. simpl.
eapply (typing_std_App).
assert (forall n, lc n C2) as lc_n_C2; eauto using coercion_lc.
rewrite (lc_open_noop _ x _ (lc_n_C2 2)).
rewrite (lc_open_noop _ x0 _ (lc_n_C2 1)). 
rewrite (lc_open_noop _ x1 _ (lc_n_C2 0)).
rewrite_env (nil ++ ((x1, t1') ::  (x0, typ_fun t1 t2) :: (x, typ_fun t1 t2) :: nil) ++ sigma).
eapply typing_std_weakening_list; eauto. 
simpl; eauto.
eapply typing_std_App.  eapply typing_std_Var. 
rewrite_env ([(x1, t1')] ++ ([(x0, typ_fun t1 t2)] ++  ((x, typ_fun t1 t2) :: sigma))). 
eapply binds_tail.  eapply binds_head. eauto.
simpl. simpl in H2. fsetdec.
eapply typing_std_App. 
assert (forall n, lc n C1) as lc_n_C1; eauto using coercion_lc.
rewrite (lc_open_noop _ x _ (lc_n_C1 2)).
rewrite (lc_open_noop _ x0 _ (lc_n_C1 1)). 
rewrite (lc_open_noop _ x1 _ (lc_n_C1 0)).
rewrite_env (nil ++ ((x1, t1') ::  (x0, typ_fun t1 t2) :: (x, typ_fun t1 t2) :: nil) ++ sigma).
eapply typing_std_weakening_list; simpl; eauto.
eapply typing_std_Var. 
rewrite_env ([(x1, t1')] ++ ([(x0, typ_fun t1 t2)] ++  ((x, typ_fun t1 t2) :: sigma))).  eauto using binds_head, binds_singleton.
rewrite_env ([(x, typ_fun t1 t2)] ++ sigma).
eauto using binds_head, binds_singleton.

Case "paircompose".
unfold compose, paircompose in *. 
eapply (typing_std_Abs (dom sigma)).
intros.  simpl. 
rewrite_env (nil ++ [(x,(typ_pair t1 t2))] ++ sigma). 
eapply typing_std_App.
assert (lc 0 C') as lc_C'; eauto using coercion_lc.
rewrite (lc_open_noop _ x _ lc_C').
   eapply typing_std_weakening; eauto || simpl; eauto.
eapply typing_std_App.
eapply (typing_std_Abs (dom ([(x,typ_pair t1 t2)] ++ sigma))).
intros.  
simpl.
eapply typing_std_Pair.
eapply (typing_std_App).
assert (forall n, lc n C1) as lc_n_C1; eauto using coercion_lc.
rewrite (lc_open_noop _ x _ (lc_n_C1 1)).
rewrite (lc_open_noop _ x0 _ (lc_n_C1 0)). 
rewrite_env (nil ++ ((x0, typ_pair t1 t2) :: (x, typ_pair t1 t2) :: nil) ++ sigma).
eapply typing_std_weakening_list; eauto. 
simpl; eauto.
eapply typing_std_Proj_1.  eapply typing_std_Var. 
rewrite_env ([(x0, typ_pair t1 t2)] ++  ((x, typ_pair t1 t2) :: sigma)).
 eapply binds_head. eauto.
eapply typing_std_App. 
assert (forall n, lc n C2) as lc_n_C2; eauto using coercion_lc.
rewrite (lc_open_noop _ x _ (lc_n_C2 1)).
rewrite (lc_open_noop _ x0 _ (lc_n_C2 0)). 
rewrite_env (nil ++ ((x0, typ_pair t1 t2) :: (x, typ_pair t1 t2) :: nil) ++ sigma).
eapply typing_std_weakening_list; simpl; eauto.
eapply typing_std_Proj_2.  eapply typing_std_Var. 
rewrite_env ([(x0, typ_pair t1 t2)] ++  ((x, typ_pair t1 t2) :: sigma)).
 eauto using  binds_head, binds_singleton.
 eapply typing_std_Var;  eauto using  binds_head, binds_singleton.
Qed.

Lemma coerce_typing : forall G m e t1 t2, 
  typing_std G m (typ_fun t1 t2) -> 
  typing_std G e t1 -> 
  typing_std G (coerce m e) t2.
intros. rename H into Tm. rename H0 into Te.
unfold coerce. 
 case_eq m; try solve [intros; subst; constructor || eauto].
 intros.
  case_eq e0; try solve [intros; subst; constructor || eauto].
 intros. subst.
  case_eq n; try solve [intros; subst; constructor || eauto].
 intros. subst.
 inversion Tm. subst. pick fresh x.  assert (x `notin` L). fsetdec.
 pose proof (H1 _ H) as Tx. simpl open_exp in Tx. inversion Tx. subst.
 destruct (binds_concat_inv _ _ _ _ _ H3) as [[notin_x_x ig] | insing].
   simpl in notin_x_x. fsetdec.
 destruct (binds_singleton_inv _ x x t2 t1 insing). subst.  eauto.
Qed.

Theorem soundness : forall sigma gamma e m t d d', 
  ok (gamma ++ sigma) -> 
  (nd_typing sigma gamma d d' e m t) ->
  (typing_std (gamma ++ sigma) m t).
Proof.
intros until 1. rename H into ok_GS. intro T.
remember (gamma++sigma) as GS.
generalize dependent GS.
induction T.
Case "fvar". intros.
subst. eauto using binds_head.
Case "base". intros.
subst; eauto using binds_tail.
Case "cast". intuition.
Case "lam". intros.
eapply (typing_std_Abs (dom GS `union` L)).
intros.
assert (x `notin` L). fsetdec.
assert (x `notin` dom GS). fsetdec.
assert (ok (([(x,t_x)]++G) ++ sigma)).
  rewrite_env ((x,t_x)::(G ++ sigma)).
  subst GS. eauto.
subst GS. rewrite_env (([(x, t_x)] ++ G) ++ sigma).
eauto.
Case "pair".
intros. intuition.
Case "app".
intros. 
unfold coerciongen in *.
eapply typing_std_App; subst GS; eauto using coercion_typing, coercion_weakening, coerce_typing.
Case "proj one".
intros. 
unfold coerciongen in *.
eapply typing_std_Proj_1; subst GS; eauto using coercion_typing, coercion_weakening, coerce_typing.
Case "proj two".
intros. 
unfold coerciongen in *.
eapply typing_std_Proj_2; subst GS; eauto using coercion_typing, coercion_weakening, coerce_typing.
Qed.

Inductive no_base : exp -> Prop :=
| No_base_bv : forall n, no_base (exp_bvar n)
| No_base_fv : forall a, no_base (exp_fvar a)
| No_base_abs : forall e t, no_base e -> no_base (exp_lam t e)
| No_base_app : forall e1 e2, no_base e1 -> no_base e2 -> no_base (exp_app e1 e2)
| No_base_pair : forall e1 e2, no_base e1 -> no_base e2 -> no_base (exp_pair e1 e2)
| No_base_proj : forall e a, no_base e -> no_base (exp_proj a e).

Hint Constructors no_base.

Lemma open_no_base_invariant : forall e x n, 
  no_base e -> 
  no_base (open_exp n (exp_fvar x) e).
Proof.
intros. generalize dependent n. generalize dependent x.
induction e; try solve [intros; inversion H; simpl; subst; eauto].
intros. simpl open_exp. destruct (n0 === n); subst; simpl; eauto.
Qed.

Theorem sufficiency : forall gamma e t d d', 
  ok gamma ->
  (typing_std gamma e t) -> 
  (no_base e) -> 
  (nd_typing nil gamma d d' e e t).
Proof.
intros gamma e t d d' okG T nb.
generalize dependent nb.
induction T.
Case "Var". eauto.
Case "Base". intros. inversion nb.
Case "Abs". intros. inversion nb. subst.
 eapply (nd_typing_Abs (dom G `union` L)).
 intros.
  assert (x `notin` L) as xnotinL.
   fsetdec.
 assert (ok ([(x,tx)]++G)) as ok_xG.
   rewrite_env ((x,tx)::G).
   eapply ok_cons; [eauto | fsetdec].
 eapply H0; eauto using open_no_base_invariant.
Case "Pair". intros. inversion nb.
   intuition.
Case "App". intros. inversion nb.
  intuition. 
     assert (coerce (id (typ_fun t' t)) e1 = e1) as e1_eq.
         eauto.
     assert (coerce (id t') e2 = e2) as e2_eq.
        eauto.
     rewrite <- e1_eq.
     rewrite <- e2_eq.
     eapply nd_typing_App; eauto; try unfold coerciongen, id; eauto.
Case "Proj one". intros. inversion nb. subst.
   intuition. 
   assert ((coerce (id (typ_pair t1 t2)) e) = e) as e_eq; eauto.
   change (nd_typing nil G d d' (exp_proj One e) (exp_proj One (coerce (id (typ_pair t1 t2)) e)) t1).
   eauto; try unfold coerciongen, id; eauto.
Case "Proj two".
   intuition. inversion nb; subst.
   assert ((coerce (id (typ_pair t1 t2)) e) = e) as e_eq; eauto.
   change (nd_typing nil G d d' (exp_proj Two e) (exp_proj Two (coerce (id (typ_pair t1 t2)) e)) t2).
   eauto; try unfold coerciongen, id; eauto.
Qed.
