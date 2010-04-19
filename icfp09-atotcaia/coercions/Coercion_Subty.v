Require Export Coercion_WF_Coerciongen.
Set Undo 100000.

Definition WF_subty (sigma:Sigma) :=
  forall f t, binds f t sigma -> 
    exists t1, exists t2, (t = (typ_fun (typ_base t1) (typ_base t2))).

Scheme coercion_dep := Induction for coercion Sort Prop.

(* Custom mutual induction principle for coercions. *)
Lemma coercion_mut_ind_strong: 
  forall
    (P : forall (l : Sigma) (l0 : pi) (a : alt) 
      (t : typ) (r : reln) (t0 : typ) (e : exp),
      coercion l l0 a t r t0 e -> Prop)
    (Q : forall (l : Sigma) (l0 : pi) (a : alt) 
      (t : typ) (r : reln) (t0 : typ) (e : exp),
      coercion l l0 a t r t0 e -> Prop),
(* P cases *)
    (forall (sigma : Sigma) (pi : pi) (a : alt) (r : reln) (t : typ),
      P sigma pi a t r t (exp_lam t (exp_bvar 0))
      (coercion_Id sigma pi a r t)) ->

    (forall (sigma : Sigma) (pi : pi) (a a' : alt) 
      (r : reln) (t1 t2 t3 : typ) (f0 : atom) (C : exp)
      (b : binds f0 (typ_fun t1 t2) sigma) (n : ~ In t2 pi)
      (t : coercion sigma (t2 :: pi) a' t2 r t3 C),
      P sigma (t2 :: pi) a' t2 r t3 C t ->
      P sigma pi a t1 r t3 (compose t1 C (exp_base f0))
      (coercion_PrimTrans sigma pi a a' r t1 t2 t3 f0 C b n t)) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_fun t1' t2') pi)
      (Carg : coercion sigma [t1'] AltSub t1' RelSub t1 C1)
      (Cret : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C'),
      (Q sigma [t1'] AltSub t1' RelSub t1 C1 Carg) ->
      (P sigma [t2] AltSub t2 RelSub t2' C2 Cret) ->
      (P sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C' Ctail) ->
      (P sigma pi AltSub (typ_fun t1 t2) RelSub t'
        (compose (typ_fun t1 t2) C' (funcompose (typ_fun t1 t2) t1' C1 C2))
        (coercion_FunTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Carg Cret Ctail))) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_pair t1' t2') pi)
      (Cfst : coercion sigma [t1] AltSub t1 RelSub t1' C1)
      (Csnd : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C'),
      (P sigma [t1] AltSub t1 RelSub t1' C1 Cfst) ->
      (P sigma [t2] AltSub t2 RelSub t2' C2 Csnd) ->
      (P sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C' Ctail) ->
      (P sigma pi AltSub (typ_pair t1 t2) RelSub t'
        (compose (typ_pair t1 t2) C' (paircompose t1 t2 C1 C2))
        (coercion_PairTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Cfst Csnd Ctail))) -> 

(* Q cases *)

    (forall (sigma : Sigma) (pi : pi) (a : alt) (r : reln) (t : typ),
      Q sigma pi a t r t (exp_lam t (exp_bvar 0))
      (coercion_Id sigma pi a r t)) ->

    (forall (sigma : Sigma) (pi : pi) (a a' : alt) 
      (r : reln) (t1 t2 t3 : typ) (f0 : atom) (C : exp)
      (b : binds f0 (typ_fun t1 t2) sigma) (n : ~ In t2 pi)
      (t : coercion sigma (t2 :: pi) a' t2 r t3 C),
      Q sigma (t2 :: pi) a' t2 r t3 C t ->
      Q sigma pi a t1 r t3 (compose t1 C (exp_base f0))
      (coercion_PrimTrans sigma pi a a' r t1 t2 t3 f0 C b n t)) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_fun t1' t2') pi)
      (Carg : coercion sigma [t1'] AltSub t1' RelSub t1 C1)
      (Cret : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C'),
      (P sigma [t1'] AltSub t1' RelSub t1 C1 Carg) ->
      (Q sigma [t2] AltSub t2 RelSub t2' C2 Cret) ->
      (Q sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C' Ctail) ->
      (Q sigma pi AltSub (typ_fun t1 t2) RelSub t'
        (compose (typ_fun t1 t2) C' (funcompose (typ_fun t1 t2) t1' C1 C2))
        (coercion_FunTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Carg Cret Ctail))) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_pair t1' t2') pi)
      (Cfst : coercion sigma [t1] AltSub t1 RelSub t1' C1)
      (Csnd : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C'),
      (Q sigma [t1] AltSub t1 RelSub t1' C1 Cfst) ->
      (Q sigma [t2] AltSub t2 RelSub t2' C2 Csnd) ->
      (Q sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C' Ctail) ->
      (Q sigma pi AltSub (typ_pair t1 t2) RelSub t'
        (compose (typ_pair t1 t2) C' (paircompose t1 t2 C1 C2))
        (coercion_PairTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Cfst Csnd Ctail))) -> 
    
    forall (l : Sigma) (l0 : pi) (a : alt) (t : typ) 
      (r : reln) (t0 : typ) (e : exp) (t1 : coercion l l0 a t r t0 e),
      (P l l0 a t r t0 e t1 /\ Q l l0 a t r t0 e t1). 
Proof.
  intros.
  induction t1 using coercion_dep ; intuition.
Qed.

Lemma coercion_mut_ind: 
  forall
    (P : forall (l : Sigma) (l0 : pi) (a : alt) 
      (t : typ) (r : reln) (t0 : typ) (e : exp),
      coercion l l0 a t r t0 e -> Prop)
    (Q : forall (l : Sigma) (l0 : pi) (a : alt) 
      (t : typ) (r : reln) (t0 : typ) (e : exp),
      coercion l l0 a t r t0 e -> Prop),
(* P cases *)
    (forall (sigma : Sigma) (pi : pi) (a : alt) (r : reln) (t : typ),
      P sigma pi a t r t (exp_lam t (exp_bvar 0))
      (coercion_Id sigma pi a r t)) ->

    (forall (sigma : Sigma) (pi : pi) (a a' : alt) 
      (r : reln) (t1 t2 t3 : typ) (f0 : atom) (C : exp)
      (b : binds f0 (typ_fun t1 t2) sigma) (n : ~ In t2 pi)
      (t : coercion sigma (t2 :: pi) a' t2 r t3 C),
      P sigma (t2 :: pi) a' t2 r t3 C t ->
      P sigma pi a t1 r t3 (compose t1 C (exp_base f0))
      (coercion_PrimTrans sigma pi a a' r t1 t2 t3 f0 C b n t)) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_fun t1' t2') pi)
      (Carg : coercion sigma [t1'] AltSub t1' RelSub t1 C1)
      (Cret : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C'),
      (Q sigma [t1'] AltSub t1' RelSub t1 C1 Carg) ->
      (P sigma [t2] AltSub t2 RelSub t2' C2 Cret) ->
      (P sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C' Ctail) ->
      (P sigma pi AltSub (typ_fun t1 t2) RelSub t'
        (compose (typ_fun t1 t2) C' (funcompose (typ_fun t1 t2) t1' C1 C2))
        (coercion_FunTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Carg Cret Ctail))) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_pair t1' t2') pi)
      (Cfst : coercion sigma [t1] AltSub t1 RelSub t1' C1)
      (Csnd : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C'),
      (P sigma [t1] AltSub t1 RelSub t1' C1 Cfst) ->
      (P sigma [t2] AltSub t2 RelSub t2' C2 Csnd) ->
      (P sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C' Ctail) ->
      (P sigma pi AltSub (typ_pair t1 t2) RelSub t'
        (compose (typ_pair t1 t2) C' (paircompose t1 t2 C1 C2))
        (coercion_PairTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Cfst Csnd Ctail))) -> 

(* Q cases *)

    (forall (sigma : Sigma) (pi : pi) (a : alt) (r : reln) (t : typ),
      Q sigma pi a t r t (exp_lam t (exp_bvar 0))
      (coercion_Id sigma pi a r t)) ->

    (forall (sigma : Sigma) (pi : pi) (a a' : alt) 
      (r : reln) (t1 t2 t3 : typ) (f0 : atom) (C : exp)
      (b : binds f0 (typ_fun t1 t2) sigma) (n : ~ In t2 pi)
      (t : coercion sigma (t2 :: pi) a' t2 r t3 C),
      Q sigma (t2 :: pi) a' t2 r t3 C t ->
      Q sigma pi a t1 r t3 (compose t1 C (exp_base f0))
      (coercion_PrimTrans sigma pi a a' r t1 t2 t3 f0 C b n t)) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_fun t1' t2') pi)
      (Carg : coercion sigma [t1'] AltSub t1' RelSub t1 C1)
      (Cret : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C'),
      (P sigma [t1'] AltSub t1' RelSub t1 C1 Carg) ->
      (Q sigma [t2] AltSub t2 RelSub t2' C2 Cret) ->
      (Q sigma (typ_fun t1' t2' :: pi) AltNoSub (typ_fun t1' t2') RelSub t' C' Ctail) ->
      (Q sigma pi AltSub (typ_fun t1 t2) RelSub t'
        (compose (typ_fun t1 t2) C' (funcompose (typ_fun t1 t2) t1' C1 C2))
        (coercion_FunTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Carg Cret Ctail))) ->
    
    (forall (sigma : Sigma) (pi : pi) (t1 t2 t' : typ) 
      (C' : exp) (t1' t2' : typ) (C1 C2 : exp)
      (n : ~ In (typ_pair t1' t2') pi)
      (Cfst : coercion sigma [t1] AltSub t1 RelSub t1' C1)
      (Csnd : coercion sigma [t2] AltSub t2 RelSub t2' C2)
      (Ctail: coercion sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C'),
      (Q sigma [t1] AltSub t1 RelSub t1' C1 Cfst) ->
      (Q sigma [t2] AltSub t2 RelSub t2' C2 Csnd) ->
      (Q sigma (typ_pair t1' t2' :: pi) AltNoSub (typ_pair t1' t2') RelSub t' C' Ctail) ->
      (Q sigma pi AltSub (typ_pair t1 t2) RelSub t'
        (compose (typ_pair t1 t2) C' (paircompose t1 t2 C1 C2))
        (coercion_PairTrans sigma pi t1 t2 t' C' t1' t2' C1 C2 n Cfst Csnd Ctail))) -> 
    
    forall (l : Sigma) (l0 : pi) (a : alt) (t : typ) 
      (r : reln) (t0 : typ) (e : exp) (t1 : coercion l l0 a t r t0 e),
      (P l l0 a t r t0 e t1).
Proof.
  intros.
  assert (P l l0 a t r t0 e t1  /\ Q l l0 a t r t0 e t1).
  eauto using coercion_mut_ind_strong.
  destruct H7. auto.
Qed. 

Inductive subty : Sigma -> typ -> typ -> Prop :=
| Subty_Id: forall sigma t, 
  (subty sigma t t) 

| Subty_Base: forall sigma t t' f, 
  (binds f (typ_fun t t') sigma) -> 
  (subty sigma t t')

| Subty_Trans : forall sigma t t1 t', 
  (subty sigma t t1) -> 
  (subty sigma t1 t') -> 
  (subty sigma t t')

| Subty_Fun : forall sigma t1 t2 t1' t2', 
  (subty sigma t1' t1) ->
  (subty sigma t2 t2') -> 
  (subty sigma (typ_fun t1 t2) (typ_fun t1' t2'))

| Subty_Pair : forall sigma t1 t2 t1' t2', 
  (subty sigma t1 t1') ->
  (subty sigma t2 t2') -> 
  (subty sigma (typ_pair t1 t2) (typ_pair t1' t2')).

Hint Constructors coercion.
Hint Resolve in_eq in_cons in_inv in_nil.
Hint Resolve coercion_pi_strengthening.
Hint Resolve insingleton.
Require Import Classical.
(* Keep uses of classic explicit
   Hint Resolve classic. *)

Lemma sub_alt_ix : forall sigma pi a t t' m, 
  (coercion sigma pi a t RelSub t' m) -> 
  (coercion sigma pi AltSub t RelSub t' m).
intros until 1. rename H into C1.
induction C1.
Case "C1 id".
 eauto.
Case "C1 prim trans".
 eauto.
Case "C1 fun trans".
 eauto.
Case "C1 pair trans".
 eauto.
Qed.

Hint Resolve sub_alt_ix.
Hint Unfold not.

Hint Resolve coercion_pi_perm.

Lemma cycle_detection_sub_deriv : forall sigma pi t t1 t' m b a a',
  (WF_subty sigma) -> 
  (t <> t1) -> 
  (In t1 pi) -> 
  (t1 = (typ_base b)) -> 
  (coercion sigma pi a t1 RelSub t' m) -> 
  (~(coercion sigma (t::pi) a' t1 RelSub t' m)) -> 
  (exists m', coercion sigma [t] AltSub t RelSub t' m').
Proof.
intros until 1. rename H into WF.
intros t_neq In_pi bf D negD. 
generalize dependent b.
generalize dependent a'.
remember RelSub as rr.
induction D.
Case "C_tail is Id".
 intros.
 pose proof (coercion_Id sigma (t::pi) a' r t0). contradiction.
Case "C_tail is PrimTrans".
 intros. 
 assert (t = t2 \/ t <> t2) as disj. eapply classic.
 destruct disj as [t_eq_t2 | t_neq_t2].
 SCase "t = t2".
   subst.
   exists C. eauto.
 SCase "t <> t2".
   assert (~(coercion sigma (t::t2::pi) a' t2 r t3 C)) as neg_t2t3.
     clear IHD.
     unfold not. intro.
     eapply negD.
       eapply coercion_PrimTrans.
         apply H.
         unfold not. intros. 
         destruct (in_inv H2); contradiction.
         assert (Permutation (t::t2::pi) (t2::t::pi)) as perm.
           assert (t2::t::pi = [t2]++(t::pi)).
              simpl. auto.
           rewrite H2.
           eapply Permutation_cons_app.
           simpl. constructor. eapply Permutation_refl.
         eauto.
   assert (exists b, t2 = (typ_base b)) as t2base.
     unfold WF_subty in WF.
     destruct (WF _ _ H) as [b1 [b2 teq]]. 
     injection teq. intros. subst. exists b2. auto.
   destruct t2base as [t2b t2eq].
   subst r.
   destruct (IHD WF t_neq_t2 (in_eq _ _) (refl_equal _) _ neg_t2t3 _ t2eq) as [MM cMM].
   exists MM. auto.
Case "FunTrans".
intros. discriminate.
Case "PairTrans".
intros. discriminate.
Qed.    

  
Hint Resolve in_ext in_not_in not_in_singleton.

Lemma funtrans_tail_is_id : forall sigma pi t1 t2 t m, 
  (WF_subty sigma) ->
  (coercion sigma pi AltNoSub (typ_fun t1 t2) RelSub t m) -> 
  (t = typ_fun t1 t2).
Proof.
intros.
remember AltNoSub as aa.
remember (typ_fun t1 t2) as tt.
induction H0.
Case "Id".
 auto.
Case "PrimTrans". subst.
  unfold WF_subty in H.
  destruct (H _ _ H0) as [T1 [T2 T_eq]].
  discriminate.
Case "FunTrans".
  discriminate.
Case "PairTrans".
  discriminate.
Qed.

Lemma altnosub_unless : forall sigma pi a t t' r m, 
  (WF_subty sigma) -> 
  (coercion sigma pi a t r t' m) -> 
  ((coercion sigma pi AltNoSub t r t' m) \/
    (exists t1, exists t2, t = typ_fun t1 t2 \/ t = typ_pair t1 t2)).
Proof.
intros until 1. rename H into WF. intro D.
induction D. 
  SCase "id".
   subst.
   left. eauto.
  SCase "primtrans".
   subst. left.
   eauto.
  SCase "funtrans". 
    right. exists t1.  exists t2. left. eauto.
  SCase "funtrans". 
    right. exists t1.  exists t2. right. eauto.
Qed.

Hint Resolve altnosub_unless.

Lemma pairtrans_tail_is_id : forall sigma pi t1 t2 t m, 
  (WF_subty sigma) ->
  (coercion sigma pi AltNoSub (typ_pair t1 t2) RelSub t m) -> 
  (t = typ_pair t1 t2).
Proof.
intros.
remember AltNoSub as aa.
remember (typ_pair t1 t2) as tt.
induction H0.
Case "Id".
 auto.
Case "PrimTrans". subst.
  unfold WF_subty in H.
  destruct (H _ _ H0) as [T1 [T2 T_eq]].
  discriminate.
Case "FunTrans".
  discriminate.
Case "PairTrans".
  discriminate.
Qed.

Lemma not_wf_sigma_fun : forall sigma f t1 t2 t, 
  (WF_subty sigma) ->
  (binds f (typ_fun (typ_fun t1 t2) t) sigma) -> 
  False.
Proof.
  intros.
  unfold WF_subty in H.
  destruct (H _ _ H0) as [b1 [b2 teq]].
  discriminate.
Qed.

Lemma not_wf_sigma_fun_inv : forall sigma f t1 t2 t, 
  (WF_subty sigma) ->
  (binds f (typ_fun t (typ_fun t1 t2)) sigma) -> 
  False.
Proof.
  intros.
  unfold WF_subty in H.
  destruct (H _ _ H0) as [b1 [b2 teq]].
  discriminate.
Qed.

Lemma not_wf_sigma_pair : forall sigma f t1 t2 t, 
  (WF_subty sigma) ->
  (binds f (typ_fun (typ_pair t1 t2) t) sigma) -> 
  False.
Proof.
  intros.
  unfold WF_subty in H.
  destruct (H _ _ H0) as [b1 [b2 teq]].
  discriminate.
Qed.

Lemma not_wf_sigma_pair_inv : forall sigma f t1 t2 t, 
  (WF_subty sigma) ->
  (binds f (typ_fun t (typ_pair t1 t2)) sigma) -> 
  False.
Proof.
  intros.
  unfold WF_subty in H.
  destruct (H _ _ H0) as [b1 [b2 teq]].
  discriminate.
Qed.

Hint Resolve funtrans_tail_is_id pairtrans_tail_is_id 
             not_wf_sigma_fun not_wf_sigma_pair 
             not_wf_sigma_fun_inv not_wf_sigma_pair_inv.

Lemma fun_shape_preserved : forall sigma pi t1 t2 t m, 
  (WF_subty sigma) -> 
  (coercion sigma pi AltSub (typ_fun t1 t2) RelSub t m) -> 
  (exists t1', exists t2', t = typ_fun t1' t2').
Proof.
intros until 1. rename H into WF. intro D.
remember (typ_fun t1 t2) as feq.
induction D.
Case "id".
        subst. exists t1. exists t2. auto.
Case "primtrans". subst.
 destruct (not_wf_sigma_fun _ _ _ _ _ WF H).
Case "funtrans".
 assert (t' = typ_fun t1' t2') as t'_eq.
   eauto.
 exists t1'. exists t2'. auto.
Case "pairtrans". discriminate.
Qed.


Lemma fun_shape_preserved_inv : forall sigma pi t1 t2 t m, 
  (WF_subty sigma) -> 
  (coercion sigma pi AltSub t RelSub (typ_fun t1 t2) m) -> 
  (exists t1', exists t2', t = typ_fun t1' t2').
Proof.
intros until 1. rename H into WF. intro D.
remember (typ_fun t1 t2) as feq.
induction D.
Case "id".
        subst. exists t1. exists t2. auto.
Case "primtrans". subst.
 destruct (IHD WF (refl_equal _)) as [t1' [t2' IH]].
 subst t3.
 destruct (not_wf_sigma_fun_inv _ _ _ _ _ WF H).
Case "funtrans".
 eauto.
Case "pairtrans".
 assert (t' = typ_pair t1' t2'). eauto.
 subst. discriminate.
Qed.


Lemma pair_shape_preserved : forall sigma pi t1 t2 t m, 
  (WF_subty sigma) -> 
  (coercion sigma pi AltSub (typ_pair t1 t2) RelSub t m) -> 
  (exists t1', exists t2', t = typ_pair t1' t2').
Proof.
intros until 1. rename H into WF. intro D.
remember (typ_pair t1 t2) as feq.
induction D.
Case "id".
        subst. exists t1. exists t2. auto.
Case "primtrans". subst.
 destruct (not_wf_sigma_pair _ _ _ _ _ WF H).
Case "funtrans".
  discriminate.
Case "pairtrans". 
 assert (t' = typ_pair t1' t2') as t'_eq.
   eauto.
 exists t1'. exists t2'. auto.
Qed.

Lemma pair_shape_preserved_inv : forall sigma pi t1 t2 t m, 
  (WF_subty sigma) -> 
  (coercion sigma pi AltSub t RelSub (typ_pair t1 t2) m) -> 
  (exists t1', exists t2', t = typ_pair t1' t2').
Proof.
intros until 1. rename H into WF. intro D.
remember (typ_pair t1 t2) as feq.
induction D.
Case "id".
        subst. exists t1. exists t2. auto.
Case "primtrans". subst.
 destruct (IHD WF (refl_equal _)) as [t1' [t2' IH]].
 subst t3.
 destruct (not_wf_sigma_pair_inv _ _ _ _ _ WF H).
Case "funtrans".
 assert (t' = typ_fun t1' t2'). eauto.
 subst. discriminate.
Case "pairtrans".
 eauto.
Qed.

Lemma funtrans_head_is_id : forall sigma pi t1 t2 t a m, 
  (WF_subty sigma) ->
  (coercion sigma pi a t RelSub (typ_fun t1 t2) m) -> 
  (coercion sigma pi AltNoSub t RelSub (typ_fun t1 t2) m) -> 
  (t = typ_fun t1 t2).
Proof.
intros.
remember (typ_fun t1 t2) as tt.
induction H0.
Case "Id".
 auto.
Case "PrimTrans". subst.
  destruct (altnosub_unless _ _ _ _ _ _ _ H H3) as [ans | [s1 [s2 [ff | pp]]]].
  pose proof (IHcoercion H ans (refl_equal _)). subst.
  destruct (not_wf_sigma_fun_inv _ _ _ _ _ H H0).
  subst.   destruct (not_wf_sigma_fun_inv _ _ _ _ _ H H0).
  subst.   destruct (not_wf_sigma_pair_inv _ _ _ _ _ H H0).
Case "FunTrans".
  symmetry. eauto.
Case "PairTrans".
  symmetry. eauto.
Qed.



Lemma pairtrans_head_is_id : forall sigma pi t1 t2 t a m, 
  (WF_subty sigma) ->
  (coercion sigma pi a t RelSub (typ_pair t1 t2) m) -> 
  (coercion sigma pi AltNoSub t RelSub (typ_pair t1 t2) m) -> 
  (t = typ_pair t1 t2).
Proof.
intros.
remember (typ_pair t1 t2) as tt.
induction H0.
Case "Id".
 auto.
Case "PrimTrans". subst.
  destruct (altnosub_unless _ _ _ _ _ _ _ H H3) as [ans | [s1 [s2 [ff | pp]]]].
  pose proof (IHcoercion H ans (refl_equal _)). subst.
  destruct (not_wf_sigma_pair_inv _ _ _ _ _ H H0).
  subst.   destruct (not_wf_sigma_fun_inv _ _ _ _ _ H H0).
  subst.   destruct (not_wf_sigma_pair_inv _ _ _ _ _ H H0).
Case "FunTrans".
  symmetry. eauto.
Case "PairTrans".
  symmetry. eauto.
Qed.


Hint Resolve fun_shape_preserved pair_shape_preserved 
             fun_shape_preserved_inv pair_shape_preserved_inv
             sym_equal funtrans_head_is_id pairtrans_head_is_id.

Lemma coercion_transitivity : forall sigma t t1 t' a1 a2 pi pi' m1 m2, 
  (WF_subty sigma) ->
  (In t pi) -> 
  (coercion sigma pi a1 t RelSub t1 m1) -> 
  (In t1 pi') -> 
  (coercion sigma pi' a2 t1 RelSub t' m2) -> 
  (exists m, coercion sigma [t] AltSub t RelSub t' m).
Proof.
intros until 1. rename H into WF. intros In_pi D1.
remember RelSub as rs.
generalize dependent pi'.
generalize dependent t'.
generalize dependent m2.
generalize dependent a2.
destruct D1 using coercion_mut_ind with
  (Q := fun sigma pi a1 t r t1 m1 (C:coercion sigma pi a1 t r t1 m1) =>
    (forall a2 m2 t' pi',
      (r = RelSub) ->
      (WF_subty sigma) -> 
      (In t pi) -> 
      (In t' pi') -> 
      (coercion sigma pi' a2 t' r t m2) -> 
      (exists m, coercion sigma [t'] AltSub t' r t1 m))).
Case "D1 identity". intros. subst.
      exists m2. eauto.
Case "D1 PrimTrans". subst r.
  intros a2 m2 t' pi' In_pi' D2.
  destruct (IHD1 WF (in_eq _ _) (refl_equal _) _ _ _ _ In_pi' D2) as [M C_ih].
    clear IHD1.
  assert ((coercion sigma (t1::[t2]) AltSub t2 RelSub t' M) \/ 
         ~(coercion sigma (t1::[t2]) AltSub t2 RelSub t' M)) as disj. eapply classic.
    destruct disj as [tailExists | tailNeg].
    SSCase "tailexists".
      exists (compose t1 M (exp_base f0)).
      eapply coercion_PrimTrans.
        apply b.
        eauto.
        assert (Permutation (t1::[t2]) (t2::[t1])).
          change (Permutation ([t1]++[t2]) ([t2]++[t1])).
          eapply Permutation_app_swap.
        eauto.
    SSCase "tailneg".
       assert (exists b, t2 = (typ_base b)) as t2base.
         unfold WF_subty in WF.
         destruct (WF _ _ b) as [b1 [b2 teq]]. 
         injection teq. intros. subst. exists b2. auto.
       destruct t2base.
       eapply cycle_detection_sub_deriv; eauto.
Case "C1 is FunTrans".
  intros a2 m2 tfinal pi' In_pi' D2.
  assert (t' = typ_fun t1' t2') as t'_eq.
    eauto.
  subst t'.
  clear IHD1_3.
  induction a2.
  SCase "a2 is AltSub".
    assert (exists s1, exists s2, (tfinal = typ_fun s1 s2)) as t'_eq.
       eauto.
    destruct t'_eq as [s1 [s2 t'_eq]].
    subst tfinal.
    assert ((typ_fun s1 s2 = typ_fun t1 t2) \/ (typ_fun s1 s2 <> typ_fun t1 t2)) as disj. eapply classic.
    destruct disj as [eq | neq].
    SSCase "s1 -> s2 = t1 -> t2".
      injection eq. intros. subst.
      exists (id (typ_fun  t1 t2)). unfold id. eauto.
    SSCase "s1 -> s2 <> t1 -> t2".
       remember (typ_fun t1' t2') as f1.
       remember (typ_fun s1 s2) as f2.
       remember AltSub as a.
       remember RelSub as r.
       induction D2.
       SSSCase "D2 is id (s1 -> s2 = t1' -> t2')". 
          subst.
          exists (compose (typ_fun t1 t2) (exp_lam (typ_fun t1' t2') (exp_bvar 0)) (funcompose (typ_fun t1 t2) t1' C1 C2)).
          eauto.
       SSSCase "D2 is primtrans... violates WF". subst.
           destruct (not_wf_sigma_fun _ _ _ _ _ WF H).
       SSSCase "D2 is funtrans... the interesting case". subst. injection Heqf1. intros. subst.
         assert (typ_fun t1'0 t2'0 = typ_fun s1 s2) as s1s2_eq.
            eauto.
         injection s1s2_eq. intros. subst.
         assert (exists marg, coercion sigma [s1] AltSub s1 RelSub t1 marg) as Darg.
            clear - subsubsubcase subsubcase D1_1 D2_1 IHD1_1 WF.
            eauto.
         assert (exists mret, coercion sigma [t2] AltSub t2 RelSub s2 mret) as Dret.          
            clear - IHD1_2 D2_2 WF.
            eauto.
         clear IHD1_1 IHD1_2 IHD2_1 IHD2_2 IHD2_3.
         destruct Dret as [mret Dret].
         destruct Darg as [marg Darg].
         exists (compose (typ_fun t1 t2) (id (typ_fun s1 s2)) (funcompose (typ_fun t1 t2) s1 marg mret)).
          unfold id.
          eauto.
        SSSCase "D2 is pairtrans ... impos".
          discriminate.
     SSCase "a2 is AltNoSub". subst.
        assert (tfinal = (typ_fun t1' t2')) as tf_eq. eauto.
        subst tfinal.
        assert (~ In (typ_fun t1' t2') [typ_fun t1 t2]) as notinsing.
          eauto.
        exists (compose (typ_fun t1 t2) (exp_lam (typ_fun t1' t2') (exp_bvar 0)) (funcompose (typ_fun t1 t2) t1' C1 C2)).
          eauto.
Case "PairTrans".
  intros a2 m2 tfinal pi' In_pi' D2.
  assert (t' = typ_pair t1' t2') as t'_eq.
    eauto.
  subst t'.
  clear IHD1_3.
  induction a2.
  SCase "a2 is AltSub".
    assert (exists s1, exists s2, (tfinal = typ_pair s1 s2)) as t'_eq.
       eauto.
    destruct t'_eq as [s1 [s2 t'_eq]].
    subst tfinal.
    assert ((typ_pair s1 s2 = typ_pair t1 t2) \/ (typ_pair s1 s2 <> typ_pair t1 t2)) as disj. eapply classic.
    destruct disj as [eq | neq].
    SSCase "s1 * s2 = t1 * t2".
      injection eq. intros. subst.
      exists (id (typ_pair  t1 t2)). unfold id. eauto.
    SSCase "s1 * s2 <> t1 * t2".
       remember (typ_pair t1' t2') as f1.
       remember (typ_pair s1 s2) as f2.
       remember AltSub as a.
       remember RelSub as r.
       induction D2.
       SSSCase "D2 is id (s1 * s2 = t1' * t2')". 
          subst.
          exists (compose (typ_pair t1 t2) (exp_lam (typ_pair t1' t2') (exp_bvar 0)) (paircompose t1 t2 C1 C2)).
          eauto.
       SSSCase "D2 is primtrans... violates WF". subst.
           destruct (not_wf_sigma_pair _ _ _ _ _ WF H).
       SSSCase "D2 is funtrans... impos". discriminate.
       SSSCase "D2 is pairtrans ... the interesting case". subst. injection Heqf1. intros. subst.
         assert (typ_pair t1'0 t2'0 = typ_pair s1 s2) as s1s2_eq.
            eauto.
         injection s1s2_eq. intros. subst.
         assert (exists mfst, coercion sigma [t1] AltSub t1 RelSub s1 mfst) as Dfst.
            clear - IHD1_1 D2_1 WF.
            eauto.
         assert (exists msnd, coercion sigma [t2] AltSub t2 RelSub s2 msnd) as Dsnd.          
            clear - IHD1_2 D2_2 WF.
            eauto.
         clear IHD1_1 IHD1_2 IHD2_1 IHD2_2 IHD2_3.
         destruct Dfst as [mfst Dfst].
         destruct Dsnd as [msnd Dsnd].
         exists (compose (typ_pair t1 t2) (id (typ_pair s1 s2)) (paircompose t1 t2 mfst msnd)).
          unfold id.
          eauto.
     SSCase "a2 is AltNoSub". subst.
        assert (tfinal = (typ_pair t1' t2')) as tf_eq. eauto.
        subst tfinal.
        assert (~ In (typ_pair t1' t2') [typ_pair t1 t2]) as notinsing.
          eauto.
        exists (compose (typ_pair t1 t2) (exp_lam (typ_pair t1' t2') (exp_bvar 0)) (paircompose  t1 t2 C1 C2)).
          eauto.
Case "Q Id". 
  rename Heqrs into t'.
  rename In_pi into m1. 
  rename WF into a1.
  intros pi' req WF In_pi In_pi' D2. subst.
      exists m1. eauto.
Case "Q D1 PrimTrans".
  rename Heqrs into t'.
  rename In_pi into m1. 
  rename WF into a1.
  intros pi' req WF In_pi In_pi' D2. subst.
  clear IHD1.
  rename t' into t.
  rename t3 into t'.
  rename f0 into f.
  remember RelSub as r.
  induction D2.
    SCase "D2 id". subst.
      exists (compose t C (exp_base f)). (* stupid eauto and existential variable instantiation *)
        eapply coercion_PrimTrans.
          apply b.
          eauto.
          eapply coercion_pi_strengthening. apply D1. 
          intros. 
          destruct (in_inv H). subst. eapply in_eq.
          assert (b0 = t). destruct (in_inv H0).  subst. auto. contradiction.
          subst.  eauto.
    SCase "D2 PrimTrans". subst.
      destruct (IHD2 b WF In_pi (in_eq _ _) D1 (refl_equal _)) as [MM cMM].
      assert ((coercion sigma (t1::[t0]) AltSub t0 RelSub t' MM) \/ 
             ~(coercion sigma (t1::[t0]) AltSub t0 RelSub t' MM)) as disj. eapply classic.
      destruct disj as [tailExists | tailNeg].
      SSSCase "tailexists".
          exists (compose t1 MM (exp_base f0)).
          eapply coercion_PrimTrans.
          apply H.
          eauto.
          assert (Permutation (t1::[t0]) (t0::[t1])).
            change (Permutation ([t1]++[t0]) ([t0]++[t1])).
            eapply Permutation_app_swap.
          eauto.
      SSSCase "tailneg".
       assert (exists b, t0 = (typ_base b)) as t0base.
         unfold WF_subty in WF.
         destruct (WF _ _ H) as [b1 [b2 teq]]. 
         injection teq. intros. subst. exists b2. auto.
       destruct t0base.
       eapply cycle_detection_sub_deriv; eauto.
    SSCase "D2 Fun Trans .. violates WF". subst.
      assert (t'0 = (typ_fun t1' t2')) as t'0_eq.
         eauto.
      subst t'0.
      destruct (not_wf_sigma_fun _ _ _ _ _ WF b).
    SSCase "D2 Pair Trans .. violates WF". subst.
      assert (t'0 = (typ_pair t1' t2')) as t'0_eq.
         eauto.
      subst t'0.
      destruct (not_wf_sigma_pair _ _ _ _ _ WF b).
Case "Q FunTrans".
  rename t' into ttmp.
  rename Heqrs into t'.
  rename In_pi into m1. 
  rename WF into a1.
  intros pi' req WF In_pi In_pi' D2. subst.
  assert (ttmp = typ_fun t1' t2') as t'_eq.
    eauto.
  subst ttmp.
  clear IHD1_3.
  induction a1.
  SCase "a2 is AltSub".
    assert (exists s1, exists s2, (t' = typ_fun s1 s2)) as t'_eq.
       eapply fun_shape_preserved_inv. eauto. eauto.
    destruct t'_eq as [s1 [s2 t'_eq]].
    subst t'.
    assert ((typ_fun s1 s2 = typ_fun t1 t2) \/ (typ_fun s1 s2 <> typ_fun t1 t2)) as disj. eapply classic.
    destruct disj as [eq | neq].
    SSCase "s1 -> s2 = t1 -> t2".
      injection eq. intros. subst.
      exists (compose (typ_fun t1 t2) (id (typ_fun t1' t2')) (funcompose (typ_fun t1 t2) t1' C1 C2)).
        unfold id.
        eauto.
    SSCase "s1 -> s2 <> t1 -> t2".
       remember (typ_fun t1' t2') as f1.
       remember (typ_fun s1 s2) as f2.
       remember (typ_fun t1 t2) as f3.
       remember AltSub as a.
       remember RelSub as r.
       induction D2.
       SSSCase "D2 is id (s1 -> s2 = t1' -> t2')". 
          subst. clear -neq. destruct neq. auto.
       SSSCase "D2 is primtrans... violates WF". subst.
           destruct (not_wf_sigma_fun _ _ _ _ _ WF H).
       SSSCase "D2 is funtrans... the interesting case". subst. intros. subst.
         assert ((typ_fun s1 s2 = typ_fun t1' t2') \/ (typ_fun s1 s2 <> typ_fun t1' t2')) as disj. eapply classic.
         destruct disj as [s1s2_eq | s1s2_neq].
         SSSSCase "s1 -> s2 = t1' -> t2'".
            injection s1s2_eq. intros. subst.
            injection Heqf2. intros. subst.
            exists (id (typ_fun t1' t2')). unfold id. eauto.
         SSSSCase "s1 -> s2 <> t1' -> t2'".
            assert (typ_fun t1'0 t2'0 = typ_fun t1 t2) as t1t2_eq.
              clear - WF D2_3.
              eauto.
            injection t1t2_eq. intros. subst. injection Heqf2. intros. subst.
            assert (exists marg, coercion sigma [t1'] AltSub t1' RelSub s1 marg) as Darg.
              clear - subsubsubcase subsubcase D1_1 D2_1 IHD1_1 WF.
              eauto.
            assert (exists mret, coercion sigma [s2] AltSub s2 RelSub t2' mret) as Dret.          
              clear - IHD1_2 D2_1 D2_2 WF.
              eauto.
            clear IHD1_1 IHD1_2 IHD2_1 IHD2_2 IHD2_3.
            destruct Dret as [mret Dret].
            destruct Darg as [marg Darg].
            exists (compose (typ_fun s1 s2) (id (typ_fun t1' t2')) (funcompose (typ_fun s1 s2) t1' marg mret)).
            unfold id.
            eauto.
        SSSCase "D2 is pairtrans ... impos".
          discriminate.
     SSCase "a2 is AltNoSub". subst.
        assert (t' = (typ_fun t1 t2)) as tf_eq. clear - WF D2. eauto.
          subst t'.
        assert (~ In (typ_fun t1' t2') [typ_fun t1 t2]) as notinsing.
          eauto.
        exists (compose (typ_fun t1 t2) (exp_lam (typ_fun t1' t2') (exp_bvar 0)) (funcompose (typ_fun t1 t2) t1' C1 C2)).
          eauto.

Case "Q PairTrans".
  rename t' into ttmp.
  rename Heqrs into t'.
  rename In_pi into m1. 
  rename WF into a1.
  intros pi' req WF In_pi In_pi' D2. subst.
  assert (ttmp = typ_pair t1' t2') as t'_eq.
    eauto.
  subst ttmp.
  clear IHD1_3.
  induction a1.
  SCase "a2 is AltSub".
    assert (exists s1, exists s2, (t' = typ_pair s1 s2)) as t'_eq.
       eapply pair_shape_preserved_inv; eauto.
    destruct t'_eq as [s1 [s2 t'_eq]].
    subst t'.
    assert ((typ_pair s1 s2 = typ_pair t1 t2) \/ (typ_pair s1 s2 <> typ_pair t1 t2)) as disj. eapply classic.
    destruct disj as [eq | neq].
    SSCase "s1 * s2 = t1 * t2".
      injection eq. intros. subst.
      exists (compose (typ_pair t1 t2) (id (typ_pair t1' t2')) (paircompose t1 t2 C1 C2)).
        unfold id.
        eauto.
    SSCase "s1 * s2 <> t1 * t2".
       remember (typ_pair t1' t2') as f1.
       remember (typ_pair s1 s2) as f2.
       remember (typ_pair t1 t2) as f3.
       remember AltSub as a.
       remember RelSub as r.
       induction D2.
       SSSCase "D2 is id (s1 * s2 = t1' * t2')". 
          subst. clear -neq. destruct neq. auto.
       SSSCase "D2 is primtrans... violates WF". subst.
           destruct (not_wf_sigma_pair _ _ _ _ _ WF H).
       SSSCase "D2 is funtrans ... impos".
          discriminate.
       SSSCase "D2 is pairtrans... the interesting case". subst. intros. subst.
         assert ((typ_pair s1 s2 = typ_pair t1' t2') \/ (typ_pair s1 s2 <> typ_pair t1' t2')) as disj. eapply classic.
         destruct disj as [s1s2_eq | s1s2_neq].
         SSSSCase "s1 * s2 = t1' * t2'".
            injection s1s2_eq. intros. subst.
            injection Heqf2. intros. subst.
            exists (id (typ_pair t1' t2')). unfold id. eauto.
         SSSSCase "s1 -> s2 <> t1' -> t2'".
            assert (typ_pair t1'0 t2'0 = typ_pair t1 t2) as t1t2_eq.
              clear - WF D2_3.
              eauto.
            injection t1t2_eq. intros. subst. injection Heqf2. intros. subst.
            assert (exists mfst, coercion sigma [s1] AltSub s1 RelSub t1' mfst) as Dfst.
              clear - subsubsubcase subsubcase D1_1 D2_1 IHD1_1 WF.
              eauto.
            assert (exists msnd, coercion sigma [s2] AltSub s2 RelSub t2' msnd) as Dsnd.          
              clear - IHD1_2 D2_1 D2_2 WF.
              eauto.
            clear IHD1_1 IHD1_2 IHD2_1 IHD2_2 IHD2_3.
            destruct Dfst as [mfst Dfst].
            destruct Dsnd as [msnd Dsnd].
            exists (compose (typ_pair s1 s2) (id (typ_pair t1' t2')) (paircompose s1 s2 mfst msnd)).
            unfold id.
            eauto.
     SSCase "a2 is AltNoSub". subst.
        assert (t' = (typ_pair t1 t2)) as tf_eq. clear - WF D2. eauto.
          subst t'.
        assert (~ In (typ_pair t1' t2') [typ_pair t1 t2]) as notinsing.
          eauto.
        exists (compose (typ_pair t1 t2) (exp_lam (typ_pair t1' t2') (exp_bvar 0)) (paircompose t1 t2 C1 C2)).
          eauto.
Qed.

  
Lemma subty_coercion : forall sigma t t', 
  (WF_subty sigma) -> 
  (subty sigma t t') -> 
  (exists m, coercion sigma [t] AltSub t RelSub t' m).
Proof.
intros sigma t t' WF S.
induction S.
Case "S Id".
intros. eauto.
Case "S Base".
intros.
 assert ((In t' [t]) \/ (not (In t' [t]))) as cl.
   eauto using classic.
 destruct cl as [t_eq_t' | t_neq_t'].
 SCase "t=t' ... m = id".
 assert (t = t'). 
   destruct (in_inv t_eq_t'). auto. contradiction.
 subst t.
 eauto.
 SCase "t <> t' ... ".
 exists (compose t (exp_lam t' (exp_bvar 0)) (exp_base f)).
 eapply coercion_PrimTrans. (* stupid eauto leaves existentials uninstantiated *)
    apply H.
    auto.
    eapply (coercion_Id sigma (t'::[t]) AltSub).
Case "S Trans (the hard case)".
destruct (IHS1 WF) as [m_t_t1 c1].
destruct (IHS2 WF) as [m_t1_t' c2].
eauto using coercion_transitivity.
Case "S Fun".
destruct (IHS1 WF) as [marg c_marg].
destruct (IHS2 WF) as [mret c_ret].
 assert ((In (typ_fun t1' t2') [(typ_fun t1 t2)]) \/ (not (In (typ_fun t1' t2') [(typ_fun t1 t2)]))) as cl.
   eauto using classic.
 destruct cl as [t_eq_t' | t_neq_t'].
 SCase "t=t' ... m = id".
 assert ((typ_fun t1 t2) = (typ_fun t1' t2')) as EQ.
   destruct (in_inv t_eq_t'). auto. contradiction.
 injection EQ. intros. subst.
 eauto.
 SCase "t <> t' ... ".
 exists (compose (typ_fun t1 t2) (exp_lam (typ_fun t1' t2') (exp_bvar 0)) (funcompose (typ_fun t1 t2) t1' marg mret)).
 eauto.
Case "S Pair".
destruct (IHS1 WF) as [mfst c_fst].
destruct (IHS2 WF) as [msnd c_snd].
 assert ((In (typ_pair t1' t2') [(typ_pair t1 t2)]) \/ (not (In (typ_pair t1' t2') [(typ_pair t1 t2)]))) as cl.
   eauto using classic.
 destruct cl as [t_eq_t' | t_neq_t'].
 SCase "t=t' ... m = id".
 assert ((typ_pair t1 t2) = (typ_pair t1' t2')) as EQ.
   destruct (in_inv t_eq_t'). auto. contradiction.
 injection EQ. intros. subst.
 eauto.
 SCase "t <> t' ... ".
 exists (compose (typ_pair t1 t2) (exp_lam (typ_pair t1' t2') (exp_bvar 0)) (paircompose t1 t2 mfst msnd)).
 eauto.
Qed.

(* Example to coq-club *)
(* Inductive T : nat -> nat -> Prop := *)
(* | T1 : forall i j k, *)
(*   T i j -> T j k -> T i k *)
(* | T2 : forall i j k,  *)
(*   T k j -> T j i -> T i k. *)

(* Lemma T_mut_ind : forall  *)
(*   (P: forall i j, T i j -> Prop) *)
(*   (Q: forall i j, T i j -> Prop),  *)
(*   (* P cases *) *)
(*   (forall i j k (t1: T i j) (t2: T j k),  *)
(*     (P i j t1) ->   *)
(*     (P j k t2) ->  *)
(*     (P i k (T1 i j k t1 t2))) -> *)
(*   (forall i j k (t1: T k j) (t2: T j i),  *)
(*     (Q k j t1) ->   *)
(*     (Q j i t2) ->  *)
(*     (P i k (T2 i j k t1 t2))) -> *)
(*   (*Q cases *)   *)
(*   (forall i j k (t1: T i j) (t2: T j k),  *)
(*     (Q i j t1) ->   *)
(*     (Q j k t2) ->  *)
(*     (Q i k (T1 i j k t1 t2))) -> *)
(*   (forall i j k (t1: T k j) (t2: T j i),  *)
(*     (P k j t1) ->   *)
(*     (P j i t2) ->  *)
(*     (Q i k (T2 i j k t1 t2))) -> *)
(*   (forall i j (t:T i j), P i j t). *)
