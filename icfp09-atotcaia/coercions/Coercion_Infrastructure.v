Require Export Coercion_Defs.
Require Import Classical.

(* ******************************************************************************** *)                                            
(* Lemmas about opening *)
(* ******************************************************************************** *)                                                                                 

Lemma open_idempotent : forall x e n, 
  (open_exp n (exp_fvar x) (open_exp n (exp_fvar x) e)) = (open_exp n (exp_fvar x) e).
Proof.
intros.
generalize dependent n. generalize dependent x.
induction e.
Case "base". intros. simpl. eauto.
Case "bvar". intros. simpl.
  destruct (n0===n). simpl. eauto.
  simpl. destruct (n0===n); try contradiction || subst; eauto.
Case "fvar". intros. simpl. eauto.
Case "cast". intros. simpl. rewrite (IHe x n). eauto.
Case "abs". intros. simpl. rewrite (IHe x (S n)). eauto.
Case "app". intros. simpl. rewrite (IHe1 x n). rewrite (IHe2 x n). eauto.
Case "pair". intros. simpl. rewrite (IHe1 x n). rewrite (IHe2 x n). eauto.
Case "proj". intros. simpl. rewrite (IHe x n). eauto.
Qed.

Inductive lc : nat -> exp -> Prop :=
| lc_bvar : forall n m, m < n -> lc n (exp_bvar m)
| lc_var : forall a n, lc n (exp_fvar a)
| lc_base : forall a n, lc n (exp_base a)
| lc_cast : forall e n t, lc n e -> lc n (exp_cast e t)
| lc_app : forall e1 e2 n, lc n e1 -> lc n e2 -> lc n (exp_app e1 e2)
| lc_pair :  forall e1 e2 n, lc n e1 -> lc n e2 -> lc n (exp_pair e1 e2)
| lc_proj : forall e n a, lc n e -> lc n (exp_proj a e)
| lc_abs : forall e n t, lc (S n) e -> lc n (exp_lam t e).


Lemma open_inverse_lc : forall e x n, 
  (lc n e) -> 
  exists e', e = (open_exp n (exp_fvar x) e') /\
    (forall f, freevars e' f -> x `notin` f).
Proof.
intros. rename H into lcn.
generalize dependent n.
induction e.
Case "base".
exists (exp_base a).
split.
  simpl; eauto.
  intros. inversion H. eauto.
Case "bvar".
intros.
inversion lcn. subst.
exists (exp_bvar n). simpl. 
   split. 
   destruct (n0 === n). 
      SCase "n0 = n".
       simpl. eauto.  subst.  assert False. omega. destruct H. 
      SCase "n0 <> n". eauto.
   intros. inversion H. eauto.
Case "fvar".
intros.
destruct (classic (a=x)).
  SCase "a=x".
   subst.
   exists (exp_bvar n).
   split.  simpl.  destruct (n===n). eauto. destruct n0.  eauto.
   intros. inversion H. subst. fsetdec.
  SCase "a<>x".
    exists (exp_fvar a).
    simpl. intuition. inversion H0. subst.
    fsetdec.
Case "cast".
intros.
inversion lcn. subst. 
destruct (IHe _ H1) as [e' [e'_eq fvs]]. 
subst. exists (exp_cast e' t). simpl.
split. eauto.
intros. eapply fvs. inversion H. eauto. 
Case "lam".
intros.
inversion lcn. subst.
destruct (IHe _ H1) as [e_body [e_body_eq fvs]].
(* destruct (increase_bvar_index e_body' x 0) as [e_body [e_body_eq fvs]]. *)
exists (exp_lam t e_body).
split.
simpl. simpl in e_body_eq. subst. simpl. f_equal.
intros. inversion H. subst. eapply fvs; eauto.
Case "app".
intros.
inversion lcn. subst. 
destruct (IHe1 _ H2) as [e1' [e1'_eq fvs1]]. 
destruct (IHe2 _ H3) as [e2' [e2'_eq fvs2]]. 
subst. exists (exp_app e1' e2'). simpl.
split. eauto.
intros. inversion H. subst.
assert (x `notin` fvs0). eapply fvs1; eauto.
assert (x `notin` fvs3). eapply fvs2; eauto.
fsetdec.
Case "pair".
intros.
inversion lcn. subst. 
destruct (IHe1 _ H2) as [e1' [e1'_eq fvs1]]. 
destruct (IHe2 _ H3) as [e2' [e2'_eq fvs2]]. 
subst. exists (exp_pair e1' e2'). simpl.
split. eauto.
intros. inversion H. subst.
assert (x `notin` fvs0). eapply fvs1; eauto.
assert (x `notin` fvs3). eapply fvs2; eauto.
fsetdec.
Case "proj".
intros.
inversion lcn. subst. 
destruct (IHe _ H1) as [e1' [e1'_eq fvs1]]. 
subst. exists (exp_proj i e1'). simpl.
split. eauto.
intros. inversion H. subst. eapply fvs1; eauto.
Qed.

Hint Constructors lc.

Lemma open_lc : forall n e x, 
  lc n (open_exp n (exp_fvar x) e) -> 
  lc (S n) e.
intros. generalize dependent n.
induction e;  try solve [intros; inversion H; subst; simpl; firstorder || eauto].
Case "bvar". intros. 
simpl in H. destruct (n0===n). subst. eauto.
  inversion H. subst.
  constructor. omega.
Qed.

Lemma coercion_lc : forall sigma pi a t d t' m, 
  (coercion sigma pi a t d t' m) -> forall n, lc n m.
Proof.
intros. generalize dependent n.
induction H.
 try repeat  (constructor; omega || firstorder).
 unfold compose. try repeat  (constructor; omega || firstorder).
 intros.  unfold compose.  unfold funcompose. try repeat  (constructor; omega || firstorder).
 intros.  unfold compose.  unfold paircompose. try repeat  (constructor; omega || firstorder).
Qed.

Lemma coerce_disjunct : forall m e, 
  (coerce m e) = e \/ (coerce m e) = (exp_app m e).
Proof.
intros m e.
case_eq m; unfold coerce; simpl; intuition.
case_eq e0; simpl; intuition.
case_eq n; simpl; intuition.
Qed.


Lemma coerce_non_identity : forall m e, 
  (forall t, m <> (id t)) -> (coerce m e) = (exp_app m e).
Proof.
intros m e m_neq_id.
case_eq m; unfold coerce; simpl; intuition.
case_eq e0; simpl; intuition.
case_eq n; simpl; intuition.
subst. unfold id in m_neq_id. destruct (m_neq_id t (refl_equal _)).
Qed.

Lemma lc_coerce: forall m e n, 
  (lc n m) -> (lc n e) -> (lc n (coerce m e)).
Proof.
intros.
destruct (coerce_disjunct m e); rewrite H1; eauto || constructor.
Qed.

Lemma typing_lc: forall sigma gamma e e' t d d', 
  nd_typing sigma gamma d d' e e' t -> 
  (lc 0 e').
Proof.
intros. rename H into T.
induction T; try solve [intros; try unfold coerciongen in *; try constructor; eauto using coercion_lc, lc_coerce || discriminate].
Case "lam".
constructor. simpl. pick fresh x. assert (x `notin` L). fsetdec.
pose proof (H0 _  H1).
eauto using open_lc.
Qed.

Lemma open_inverse_nd : forall sigma gamma e x tx e' t d d', 
  ok sigma -> ok ([(x,tx)]++gamma) -> 
  nd_typing sigma ([(x,tx)]++gamma) d d' e e' t -> 
  (exists e0, (e' = (open_exp 0 (exp_fvar x) e0)) /\ (forall f, freevars e0 f -> x `notin` f)).
Proof.
intros. eauto using typing_lc, open_inverse_lc.
Qed.


Lemma open_exp_injection : forall e1 e2 y n fv1 fv2, 
  (freevars e1 fv1) -> 
  (freevars e2 fv2) -> 
  (y `notin` fv1) -> 
  (y `notin` fv2) -> 
  (open_exp n (exp_fvar y) e1) = (open_exp n (exp_fvar y) e2) ->
  e1 = e2.
Proof.
intros e1 e2 y n fv1 fv2 freevars1 freevars2 y_notin_1 y_notin_2 eq. 
generalize dependent n.
generalize dependent e2.
generalize dependent fv1.
generalize dependent fv2.
induction e1.
Case "base".
intros.
simpl in eq. 
induction e2; simpl in eq; subst; try eauto || discriminate || (destruct (n===n0); subst; discriminate).
Case "bvar".
intros. simpl in eq.
induction e2.
 SCase "e2 base".
 destruct (n0===n); subst; discriminate.
 SCase "e2 bvar".
 simpl in eq.
  destruct (n0===n1) as [n0_eq_n1 | n0_neq_n1].
     SSCase "n0_eq_n1".
       subst. 
       destruct (n1===n) as [n1_eq_n | n1_neq_n].
         subst. eauto.
         discriminate.
     SSCase "n0_neq_n1".
        destruct (n0===n); subst; eauto || discriminate.
 SCase "e2 fvar".
   simpl in eq.
   destruct (n0===n).
      subst. assert (y=a). injection eq; intuition.
   subst. inversion freevars2. subst. fsetdec. eauto.
 destruct (n0===n); subst; discriminate.
 destruct (n0===n); subst; discriminate.
 destruct (n0===n); subst; discriminate.
 destruct (n0===n); subst; discriminate.
 destruct (n0===n); subst; discriminate.
Case "fvar".
 intros.
 simpl in eq.
 induction e2; simpl in eq; try eauto || destruct (n===n0); subst; try discriminate || eauto.
 assert (y=a). injection eq; intuition.
  subst. inversion freevars1. subst. fsetdec. eauto.
Case "Cast".
 intros.
 simpl in eq.
 induction e2; simpl in eq; try eauto || destruct (n===n0); subst; try discriminate || eauto.
 inversion freevars1. subst.
 injection eq;  intros. subst.
 inversion freevars2. subst. 
 assert (e1 = e2). eapply (IHe1 fv2); eauto. subst; auto.
Case "Abs".
 intros.
 simpl in eq.
 induction e2; simpl in eq; try eauto || destruct (n===n0); subst; try discriminate || eauto.
 inversion freevars1. subst.
 firstorder.
 injection eq. intros. subst.
 inversion freevars2. subst. 
 assert (e1 = e2). eapply (IHe1 fv2); eauto. subst; eauto.
Case "App".
 intros.
 simpl in eq.
 induction e2; simpl in eq; try eauto || destruct (n===n0); subst; try discriminate || eauto.
 inversion freevars1. subst.
 injection eq. intros. subst.
 inversion freevars2. subst. 
 assert (e1_1 = e2_1). eapply (IHe1_1 fvs0); try fsetdec || eauto.
 assert (e1_2 = e2_2). eapply (IHe1_2 fvs3); try fsetdec || eauto.
 subst. eauto.
Case "Pair".
 intros.
 simpl in eq.
 induction e2; simpl in eq; try eauto || destruct (n===n0); subst; try discriminate || eauto.
 inversion freevars1. subst.
 injection eq. intros. subst.
 inversion freevars2. subst. 
 assert (e1_1 = e2_1). eapply (IHe1_1 fvs0); try fsetdec || eauto.
 assert (e1_2 = e2_2). eapply (IHe1_2 fvs3); try fsetdec || eauto.
 subst. eauto.
Case "Proj".
 intros.
 simpl in eq.
 induction e2; simpl in eq; try eauto || destruct (n===n0); subst; try discriminate || eauto.
 inversion freevars1. subst.
 injection eq. intros. subst.
 inversion freevars2. subst. 
 assert (e1 = e2). eapply (IHe1 fv2); try fsetdec || eauto.
 subst. eauto.
Qed.
 

Lemma freevars_totality : forall e, exists fvs, freevars e fvs.
Proof.
intros.
induction e.
Case "base".
exists AtomSet.F.empty. constructor.
Case "bvar".
exists AtomSet.F.empty. constructor.
Case "fvar".
exists (singleton a). constructor.
Case "cast".
destruct IHe as [fvse].
exists fvse; constructor; eauto.
Case "lam".
destruct IHe as [fvse].
exists fvse; constructor; eauto.
Case "app".
destruct IHe1 as [fvse1].
destruct IHe2 as [fvse2].
exists (fvse1 `union` fvse2); constructor; eauto.
Case "pair".
destruct IHe1 as [fvse1].
destruct IHe2 as [fvse2].
exists (fvse1 `union` fvse2); constructor; eauto.
Case "proj".
destruct IHe as [fvse].
exists fvse; constructor; eauto.
Qed.


Lemma binds_id : forall x (t1:typ) t2 G, 
  ok G -> 
  binds x t1 G -> 
  binds x t2 G -> 
  (t1 = t2).
Proof.
intros.
induction G.
Case "G is nil".
inversion H0.
Case "G is cons".
rewrite_env ([a] ++ G) in H0.
destruct (binds_concat_inv _ _ _ _ _ H0) as [[xNotinA xinG] | xinA].
SCase "xinG".
rewrite_env ([a] ++ G) in H1.
destruct (binds_concat_inv _ _ _ _ _ H1) as [[xNotinA' xinG'] | xinA'].
SSCase "xinG'".
eapply IHG; try inversion H; eauto.
SSCase "xinA'".
pose proof (binds_In _ _ _ _ xinA'). contradiction.
SCase "xinA".
rewrite_env ([a] ++ G) in H1.
destruct (binds_concat_inv _ _ _ _ _ H1) as [[xNotinA' xinG'] | xinA'].
SSCase "xinG'".
pose proof (binds_In _ _ _ _ xinA). contradiction.
SSCase "xinA".
induction a.
destruct (binds_singleton_inv _ _ _ _ _ xinA) as [ A B].
destruct (binds_singleton_inv _ _ _ _ _ xinA') as [ C D].
subst. auto.
Qed.


Lemma opening_preserves_identity : forall x i e1 e2 fvs1 fvs2, 
  (freevars e1 fvs1) ->   
  (freevars e2 fvs2) -> 
  (x `notin` fvs1) -> (x `notin` fvs2) -> 
  ((open_exp i (exp_fvar x) e1) = (open_exp i (exp_fvar x) e2)) -> e1 = e2.
Proof.
Lemma freevar_neq : forall x e fvs, 
  (freevars e fvs) ->   
  (x `notin` fvs) -> 
  (exp_fvar x) <> e.
Proof. 
intros.
induction e; 
  try discriminate || 
    inversion H. subst fvs. assert (x <> a); [fsetdec | injection; auto].
Qed.
intros.
generalize dependent e2.
generalize dependent i.
generalize dependent fvs1.
generalize dependent fvs2.
induction e1.
Case "exp_base".
  intros.
  assert ((exp_fvar x) <> e2) as Neq2. eauto using freevar_neq.
  induction e2; simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])). 
Case "exp_bvar".
  intros.
  induction e2.
  SCase "exp_base".
  simpl open_exp in H3.
  destruct (i===n). subst. discriminate. auto. 
  SCase "exp_bvar".
  simpl open_exp in H3.
  destruct (i===n). destruct (i===n0). subst. subst. auto.
  discriminate.
  destruct (i===n0);
  auto. discriminate. 
  SCase "exp_fvar".
  simpl open_exp in H3.
  destruct (i===n).
  assert ((exp_fvar x) <> (exp_fvar a)) as Neq2. eauto using freevar_neq.
  destruct Neq2. auto. auto.
  SCase "exp_cast".
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
  SCase "exp_lam".
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
  SCase "exp_app".
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
  SCase "exp_pair".
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
  SCase "exp_proj".
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
Case "exp_fvar".
  intros.
  assert ((exp_fvar x) <> (exp_fvar a)) as Neq1. eauto using freevar_neq.
  induction e2; simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; destruct Neq1; auto | auto])).
Case "exp_cast".
  induction e2.
  SCase "exp_base".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_bvar".
  intros.
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
  SCase "exp_fvar".
  intros.
  assert ((exp_fvar x) <> (exp_fvar a)) as Neq1. eauto using freevar_neq.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; destruct Neq1; auto | auto])).
  SCase "exp_cast".
  intros.
  simpl open_exp in H3.
  injection H3. intros bodyEq tEq.
  inversion H. inversion H0.
  assert (e1=e2) as fromIH.
  eapply (IHe1 fvs2); eauto || fsetdec.
  subst. auto.
  SCase "exp_lam".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_app".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_pair".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_proj".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
Case "exp_lam".
  induction e2.
  SCase "exp_base".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_bvar".
  intros.
  simpl open_exp in H3.
  destruct (i===n); discriminate H3.
  SCase "exp_fvar".
  intros.
  assert ((exp_fvar x) <> (exp_fvar a)) as Neq1. eauto using freevar_neq.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; destruct Neq1; auto | auto])).
  SCase "exp_case".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_lam".
  intros.
  simpl open_exp in H3.
  injection H3. intros bodyEq tEq.
  inversion H. inversion H0.
  assert (e1=e2) as fromIH.
  eapply (IHe1 fvs2); eauto || fsetdec.
  subst. auto.
  SCase "exp_app".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_pair".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
  SCase "exp_proj".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
Case "exp_app".
  induction e2.
   SCase "exp_base".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_bvar".
   intros.
   simpl open_exp in H3.
   destruct (i===n); discriminate H3.
   SCase "exp_fvar".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_case".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_lam".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_app".
   intros.
   simpl open_exp in H3. injection H3. intros Eq2 Eq1.
   assert (e1_1 = e2_1) as fromIH1.
   inversion H. inversion H0. eapply (IHe1_1 fvs4);  eauto || fsetdec.
   assert (e1_2 = e2_2) as fromIH2.
   inversion H. inversion H0. eapply (IHe1_2 fvs5);  eauto || fsetdec.
   subst. auto.
   SCase "exp_pair".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_proj".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
Case "exp_pair".
  induction e2.
   SCase "exp_base".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_bvar".
   intros.
   simpl open_exp in H3.
   destruct (i===n); discriminate H3.
   SCase "exp_fvar".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_case".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_lam".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_app".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_pair".
   intros.
   simpl open_exp in H3. injection H3. intros Eq2 Eq1.
   assert (e1_1 = e2_1) as fromIH1.
   inversion H. inversion H0. eapply (IHe1_1 fvs4);  eauto || fsetdec.
   assert (e1_2 = e2_2) as fromIH2.
   inversion H. inversion H0. eapply (IHe1_2 fvs5);  eauto || fsetdec.
   subst. auto.
   SCase "exp_proj".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
Case "exp_proj".
  induction e2.
   SCase "exp_base".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_bvar".
   intros.
   simpl open_exp in H3.
   destruct (i0===n); discriminate H3.
   SCase "exp_fvar".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_case".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_lam".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_app".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_pair".
   intros.
   simpl open_exp in H3; (auto || discriminate ||  (destruct (i===n); [subst; discriminate | auto])).
   SCase "exp_proj". 
   intros.
   simpl open_exp in H3. injection H3. intros Eq2 Eq1.
   assert (e1 = e2) as fromIH1.
   inversion H. inversion H0. eapply (IHe1 fvs2);  eauto || fsetdec.
   subst. auto.
Qed.

(* ******************************************************************************** *)
(* Common structural properties about coercion generation *)
(* ******************************************************************************** *)

Lemma coercion_pi_strengthening: forall sigma pi pi' t t' C a r, 
  coercion sigma pi a t r t' C -> 
  (forall b, In b pi' -> In b pi) ->
    coercion sigma pi' a t r t' C.
Proof.
intros until 1. rename H into D1. intro subset.
generalize dependent pi'.
induction D1.
Case "coercion_Id".
intros; eapply coercion_Id; eauto.
Case "coercion_PrimTrans".
intros.
eapply coercion_PrimTrans.
eauto. unfold not; intro contra.
pose proof (subset _ contra). contradiction.
eapply IHD1.
intros b inCons.
destruct (in_inv inCons) as [head | tail].
subst. eauto using in_eq.
eapply in_cons. eauto using subset.
Case "coercion_FunTrans".
intros.
eapply coercion_FunTrans.
unfold not; intro contra.
(* weird ... Coq doesn't like this *)
(* pose proof (subset (typ_fun t1' t2') contra).  *)
assert (In (typ_fun t1' t2') pi). 
eauto. contradiction.
auto. auto.
eapply IHD1_3.
intros b inCons.
destruct (in_inv inCons) as [head | tail].
subst. eauto using in_eq.
eapply in_cons. eauto using subset.
Case "coercion_PairTrans".
intros.
eapply coercion_PairTrans.
unfold not; intro contra.
(* weird ... Coq doesn't like this *)
(* pose proof (subset (typ_fun t1' t2') contra).  *)
assert (In (typ_pair t1' t2') pi). 
eauto. contradiction.
auto. auto.
eapply IHD1_3.
intros b inCons.
destruct (in_inv inCons) as [head | tail].
subst. eauto using in_eq.
eapply in_cons. eauto using subset.
Qed.

Hint Constructors coercion.
Hint Resolve Permutation_in Permutation_sym Permutation_refl Permutation_trans.

Lemma perm_cons : forall A (t:A) pi pi', 
  Permutation pi pi' -> 
  Permutation (t::pi) (t::pi').
Proof.
intros.
  change (Permutation ([t]++pi) ([t]++pi')). eauto using Permutation_app_head.
Qed.

Lemma coercion_pi_perm: forall sigma pi pi' a t r t' m, 
  (coercion sigma pi a t r t' m) -> 
  (Permutation pi pi') -> 
  (coercion sigma pi' a t r t' m).
Proof with eauto*.
intros. rename H into C. rename H0 into P.
generalize dependent pi'.
induction C.
Case "id".
intros. eauto. 
Case "prim trans".
intros.
eapply coercion_PrimTrans. 
  eauto.
  try unfold not; eauto.
  assert (Permutation (t2::pi) (t2::pi')). eauto using perm_cons.
  firstorder.
Case "fun trans".
  intros. 
eapply coercion_FunTrans. unfold not; eauto. eauto. eauto. 
  assert (Permutation ((typ_fun t1' t2')::pi) ((typ_fun t1' t2')::pi')). eauto using perm_cons.
  firstorder.
Case "pair trans".
  intros. 
eapply coercion_PairTrans. unfold not; eauto. eauto. eauto. 
  assert (Permutation ((typ_pair t1' t2')::pi) ((typ_pair t1' t2')::pi')). eauto using perm_cons.
  firstorder.
Qed.


(* ******************************************************************************** *)
(* Lemmas about lists *)
(* ******************************************************************************** *)
Lemma in_inv_nodup : forall (A:Type) (a:A) (b:A) (l:list A), 
  (In b (a::l)) -> 
  (NoDup (a::l)) -> 
  ((a=b /\ ~In b l) \/ (a<>b /\ In b l)).
Proof.
intros A a b l Inb_al Nodup.
inversion Nodup. subst x. subst l0.
destruct (in_inv Inb_al) as [aEqb | inTl].
  Case "a=b".
  left. subst b.
  eauto.
  Case "In tl".
  right.
  split.
  unfold not. intro. subst b. contradiction.
  auto.
Qed.

  
Lemma in_singleton_eq : 
forall (A:Type) (a:A) (l:list A) (b:A), 
  (In b l) -> 
  (NoDup l) ->
  (forall c, In c l -> In c [a]) -> 
  l = [a].
Proof.
intros A a l.
induction l.
Case "l nil".
intros.
  contradiction.
Case "l cons".
intros.
assert (a=a0).
 pose proof (H1 a0 (in_eq _ _)).
 inversion H2. auto. destruct H3.
 subst a0.
cut (l=nil). intros. subst l. eauto.
SCase "cut l=nil".
destruct (in_inv_nodup _ _ _ l H H0) as [ [aEqb xx] | [aNeqb  bInl]].
  SSCase "a = b".
   subst b.
   induction l. auto.
   clear IHl0.
   inversion H0. subst x. subst l0.
   assert (forall c:A, In c (a0::l) -> In c [a]).
     intros. 
      eapply H1. eapply in_cons. eauto.
   pose proof (IHl a0 (in_eq _ _) H5 H2).
   injection H3. intros. subst a0. 
   unfold not in H4. destruct (H4 (in_eq _ _)).
  SSCase "a <> b AND b in L".
  pose proof (H1 b (in_cons _ _ _ bInl)).
  destruct H2. contradiction. destruct H2.
Qed.

Lemma in_singleton_pair : forall (A:Type) (B:Type) (a:A) (b:B) c d, 
  In (a,b) [(c,d)] -> a = c /\ b = d.
Proof.
intros.
destruct (in_inv H).
      SSSSCase "in head".
         injection H0. intros. subst a b. auto.
      SSSSCase "silly in nil". contradiction.
Qed.  

Lemma in_sing_eq_l : forall (x:exp) (y:typ) a b,
  In (x,y) [(a,b)] -> 
  x = a.
Proof.
intros.
destruct (in_inv H).
  injection H0. intros. subst. intuition.
contradiction.
Qed.

Lemma in_sing_eq_r : forall (x:exp) (y:typ) a b,
  In (x,y) [(a,b)] -> 
  y = b.
Proof.
intros.
destruct (in_inv H).
  injection H0. intros. subst. intuition.
contradiction.
Qed.

Lemma insingleton : forall (A:Type) (a:A) theta, 
  In a theta -> (forall b:A, In b [a] -> In b theta).
  intros. assert (a = b).
  destruct (in_inv H0). subst a. auto. contradiction. subst. auto.
  Qed.

Lemma in_ext : forall (A:Type) (x:A) l l', 
  In x l -> In x (l ++ l').
Proof.
intros.
eauto using in_or_app.
Qed.

Lemma in_not_in : forall (A:Type) (x:A) (y:A) l, 
  In x l -> ~ In y l -> x <> y.
Proof.
intros. unfold not. intros. subst. contradiction.
Qed.


Lemma not_in_singleton : forall (A:Type) (x:A) y, 
  x <> y -> ~In x [y].
intros.
unfold not. intros.
destruct (in_inv H0). subst. destruct H. reflexivity. contradiction.
Qed.
