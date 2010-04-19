Require Export Coercion_WF_Coerciongen.
Require Import Classical.
Hint Resolve in_eq in_cons in_inv in_nil.
Hint Resolve insingleton open_exp_injection.
Hint Unfold coerciongen id coerce.


(* ******************************************************************************** *)
(* Set-based coercion insertion system *)
(* ******************************************************************************** *)

Definition MType:Type := list(exp*typ).

Definition open_exp_list (k:nat) (e:exp) (M:list (exp*typ)) : list (exp * typ) :=
  List.map (fun et => (open_exp k e (fst et), snd et)) M.

Inductive Abs : MType -> typ -> MType -> Prop :=
| Abs_cons : forall M1 tx M, 
  (NoDup M) -> 
  (forall e' t', 
    (In (e',t') M) ->
    (exists t, exists e, 
      ((e' = exp_lam tx e) /\
        (t' = typ_fun tx t) /\
        In (e,t) M1))) -> 
  (forall e t, 
    (In (e,t) M1) -> (In (exp_lam tx e, typ_fun tx t) M)) ->
  Abs M1 tx M.

Inductive Pair : MType -> MType -> MType -> Prop :=
| Pair_cons :
  forall M1 M2 M, 
    (NoDup M) ->
    (forall e t, 
      (In (e,t) M) -> 
      (exists m1, exists m2, exists t1, exists t2, 
        (e = (exp_pair m1 m2)) /\
        (t = (typ_pair t1 t2)) /\
        (In (m1, t1) M1) /\ 
        In (m2, t2) M2)) -> 
    (forall m1 t1 m2 t2, 
      (In (m1, t1) M1) -> (In (m2, t2) M2) -> 
      (In (exp_pair m1 m2, (typ_pair t1 t2)) M)) ->
    (Pair M1 M2 M)
.


Inductive Tofun : Sigma -> MType -> MType -> Prop :=
| Tofun_cons:
  forall sigma M1 M,
    (NoDup M) ->
    (forall e t t1 t2 m,
      In (e,t) M1 -> 
      coerciongen sigma t RelPrim (typ_fun t1 t2) m -> 
      (In ((coerce m e), typ_fun t1 t2) M)) -> 
    (forall e t,
      (In (e,t) M) -> 
      (exists e1, exists m, exists t1, exists t2, exists t', 
        (e = (coerce m e1)) /\
        (t = (typ_fun t1 t2)) /\
        (coerciongen sigma t' RelPrim (typ_fun t1 t2) m) /\
        (In (e1,t') M1))) ->
    (Tofun sigma M1 M)
    .


Inductive App : Sigma -> MType -> MType -> MType -> Prop :=
| App_cons : 
  forall sigma M1 M2 M Mf, 
    (NoDup M) ->
    (Tofun sigma M1 Mf) -> 
    (forall e1 t1 t2 e2 t1' c,
      (In (e1, (typ_fun t1 t2)) Mf) -> 
      (In (e2,t1') M2) -> 
      (coerciongen sigma t1' RelSub t1 c) ->
      (In ((exp_app e1 (coerce c e2)), t2) M)) -> 
    (forall e t, 
      (In (e,t) M) -> 
      exists e1, exists c, exists e2, exists t1, exists t1', 
        (e = (exp_app e1 (coerce c e2))) /\
        (In (e1, (typ_fun t1 t)) Mf) /\
        (In (e2, t1') M2) /\
        (coerciongen sigma t1' RelSub t1 c)) -> 
    (App sigma M1 M2 M).

Inductive Proj : Sigma -> MType -> ix -> MType -> Prop :=
| Proj_cons :
  forall sigma M' i M, 
    (NoDup M) ->
    (forall e t t1 t2 c,
      (In (e,t) M') ->
      (coerciongen sigma t RelPrim (typ_pair t1 t2) c) ->
      (exists t', 
        ((i = One -> t' = t1) /\
          (i = Two -> t' = t2) /\
          (In ((exp_proj i (coerce c e)), t') M)))) -> 
    (forall e t, 
      (In (e,t) M) -> 
      exists c, exists e', exists t', exists t1, exists t2, 
        (e = (exp_proj i (coerce c e'))) /\
        In (e', t') M' /\ 
        coerciongen sigma t' RelPrim (typ_pair t1 t2) c /\
        (i = One -> t = t1) /\
        (i = Two -> t = t2)) -> 
    (Proj sigma M' i M).

(* Coercion insertion *)
Inductive typing : Sigma -> Gamma -> exp -> list (exp * typ) -> Prop :=
| typing_Var :
  forall sigma G x t, 
    (binds x t G) -> 
    (typing sigma G (exp_fvar x) [((exp_fvar x),t)])
    
| typing_Base : 
  forall sigma G b t,
    (binds b t sigma) -> 
    (typing sigma G (exp_base b) [((exp_base b),t)])

| typing_Cast :
  forall sigma G e t M M', 
    (typing sigma G e M) -> 
    (forall e' t', In (e',t') M' -> (t'=t /\ In (e',t') M)) -> 
    (forall e', In (e',t) M -> In (e',t) M') ->
    (NoDup M') ->
    (typing sigma G (exp_cast e t) M')
    
| typing_Abs : 
  forall L sigma G t_x e M M', 
    (forall x, x `notin` L -> 
      (typing sigma ([(x,t_x)] ++ G) (open_exp 0 (exp_fvar x) e) (open_exp_list 0 (exp_fvar x) M))) -> 
    (Abs M t_x M') ->
    (typing sigma G (exp_lam t_x e) M')

| typing_Pair : 
  forall sigma G e1 e2 M1 M2 M, 
    (typing sigma G e1 M1) -> 
    (typing sigma G e2 M2) -> 
    (Pair M1 M2 M) -> 
    (typing sigma G (exp_pair e1 e2) M)
    
| typing_App :
  forall sigma G e1 M1 e2 M2 M,
    (typing sigma G e1 M1) -> 
    (typing sigma G e2 M2) -> 
    (App sigma M1 M2 M) -> 
    (typing sigma G (exp_app e1 e2) M)

| typing_Proj :
  forall sigma G e i M M',
    (typing sigma G e M) -> 
    (Proj sigma M i M') -> 
    (typing sigma G (exp_proj i e) M')
.

Inductive Filter : MType -> typ -> MType -> Prop :=
| Filter_nil : forall t, Filter nil t nil
| Filter_cons_in :
  forall M1 t M2 e, 
    (Filter M1 t M2) -> 
    (Filter ((e,t)::M1) t ((e,t)::M2))
| Filter_cons_notin :
  forall M1 t M2 e t', 
    (Filter M1 t M2) -> 
    (t <> t') -> 
    (Filter ((e,t')::M1) t M2).

(* ******************************************************************************** *)
(* Lemmas regarding structural properties of typing *)
(* ******************************************************************************** *)

Lemma nodup_typing_M : forall sigma G e M, 
  typing sigma G e M -> NoDup M.
Admitted.

Lemma open_inverse : forall sigma gamma e x tx M E t,
  ok sigma -> ok ([(x,tx)]++gamma) ->
  typing sigma ([(x,tx)]++gamma) (open_exp 0 (exp_fvar x) e) M ->
  (In (E,t) M) ->
  (exists e', E = (open_exp 0 (exp_fvar x) e')).
Admitted.

Lemma open_inverse_list : forall sigma gamma e x tx M,
  ok sigma -> ok ([(x,tx)]++gamma) ->
  typing sigma ([(x,tx)]++gamma) (open_exp 0 (exp_fvar x) e) M ->
  (exists M', M = (open_exp_list 0 (exp_fvar x) M') /\
    (forall e t,
      In (e, t) M ->
      exists e', e = (open_exp 0 (exp_fvar x) e') /\ In (e',t) M')).
Admitted.

Hint Constructors coercion typing nd_typing.
Definition emptyM:MType := nil.
Hint Unfold emptyM.
Hint Constructors Filter.

Lemma tofun_deterministic: forall sigma M1 M2 M3, 
  Tofun sigma M1 M2 -> 
  Tofun sigma M1 M3 -> 
  forall x, In x M2 -> In x M3.
Admitted.

Lemma Abs_totality : forall M tx, 
  exists M', Abs M tx M'.
Admitted.

Lemma Pair_totality : forall M1 M2, 
  exists M, Pair M1 M2 M.
Admitted.

Lemma App_totality : forall sigma M1 M2, 
  exists M, App sigma M1 M2 M.
Admitted.

Lemma Proj_totality : forall sigma M ix, 
  exists M', Proj sigma M ix M'.
Admitted.      



Lemma Pair_convenience : forall M1 M2 M e1 t1 e2 t2,
  Pair M1 M2 M -> 
  In (e1, t1) M1 -> 
  In (e2, t2) M2 -> 
  In (exp_pair e1 e2, typ_pair t1 t2) M.
Admitted.

Lemma filter_totality: forall M t, exists M', Filter M t M'.
Proof.
intros.
induction M.
Case "M Nil".
exists emptyM. constructor; firstorder.
Case "M cons".
destruct IHM as [M' FM'].
destruct a as [e' t'].
assert ((t=t') \/ (t<>t')) as eq_disj. eapply classic.
destruct eq_disj as [t_eq_t' | t_neq_t'].
  SCase "t_eq_t'".
    subst t'.
    exists ((e',t)::M').
    constructor. firstorder.
  SCase "t_neq_t'".
    exists M'.
    constructor; firstorder.
Qed.
 
Lemma filter_sufficiency_1 : forall M t M', 
  Filter M t M' -> 
  (forall e' t', In (e', t') M' -> (t'=t) /\ In (e',t') M).
intros until 1. rename H into filter.
induction filter.
Case "nil". firstorder.
Case "cons in".
intros e' t' in_cons_m2. 
destruct (in_inv in_cons_m2) as [in_hd | in_M2].
  SCase "in hd".
   injection in_hd. intros. subst. firstorder.
  SCase "in tl". firstorder.
Case "cons not in". firstorder.
Qed. 

Lemma filter_sufficiency_2 : forall M t M', 
  Filter M t M' -> 
  (forall e', In (e', t) M -> In (e',t) M').
intros until 1. rename H into filter.
induction filter.
Case "nil". firstorder.
Case "cons in". firstorder.
Case "cons not in". 
intros e' In_cons_M1. 
destruct (in_inv In_cons_M1) as [in_hd | in_M1].
  SCase "in_hd". injection in_hd. intros. subst. intuition.
  SCase "in_M1". firstorder.
Qed.

Lemma filter_sufficiency_3: forall M t M', 
  Filter M t M' -> NoDup M -> NoDup M'.
Proof.
intros until 1. rename H into filter. intro nodup_M.
induction filter.
Case "nil".
  eauto.
Case "cons in".
  constructor.
  unfold not; intro.
  assert (In (e,t) M1).
   pose proof (filter_sufficiency_1 _ _ _ filter) as fs1.
   firstorder. eauto.
   inversion nodup_M. eauto.
   inversion nodup_M. eauto.
Case "cons not in".
   inversion nodup_M; eauto.
Qed.

Hint Resolve filter_sufficiency_1 filter_sufficiency_2 filter_sufficiency_3 nodup_typing_M.
Hint Constructors NoDup.

Lemma nd_typing_implies_typing : forall sigma G e e' t, 
  (ok sigma) -> (ok G) -> 
  (nd_typing sigma G e e' t) -> 
  (exists M, typing sigma G e M /\ In (e', t) M).
intros until 1. rename H into ok_sigma. intros ok_G ND_t.
induction ND_t.
Case "nd_typing_var".
exists ([(exp_fvar x, t)]). intuition.
Case "nd_typing_base".
exists ([(exp_base b, t)]). intuition. 
Case "nd_typing_cast".
destruct (IHND_t ok_sigma ok_G) as [M_e [typing_e In_M]].
destruct (filter_totality M_e t) as [M' filter_M_M'].
exists M'. split. 
  SCase "Left".
    pose proof (filter_sufficiency_1 _ _ _ filter_M_M') as fs1.
    pose proof (filter_sufficiency_2 _ _ _ filter_M_M') as fs2.
    pose proof (filter_sufficiency_3 _ _ _ filter_M_M') as fs3.
    apply (typing_Cast sigma G e t M_e M'); 
      firstorder with nodup_typing_M.
  SCase "Right".
    eauto.
Case "nd_typing_abs".
 destruct (freevars_totality e) as [fvs fvse].
 pick fresh y.
 assert (y `notin` L) as ynotinL.
   fsetdec.
 assert (ok ([(y,t_x)]++G)) as ok_yG.
   rewrite_env ((y,t_x)::G).
   eapply ok_cons; [eauto | fsetdec].
 destruct (H0 y ynotinL ok_sigma ok_yG) as [M [Typing I]].
 destruct (open_inverse_list _ _ _ _ _ _ ok_sigma ok_yG Typing) as [M' [M'_eq In_M']].
 destruct (In_M' _ _ I) as [E' [E'_eq In_E']].
 assert (e' = E'). eauto.
 subst E'.
 clear H0 In_M'.
 destruct (Abs_totality M' t_x) as [N AbsN].
 exists N.
 split.
 SCase "typing".
   eapply typing_Abs.
   intros.
   eapply (opening_name_irrelevance sigma G y).
     eauto.
     fsetdec.
     subst M. apply Typing.
     apply H0. auto.
 SCase "In AbsFun".
   inversion AbsN. subst.
   eauto. 
Case "nd_typing_pair".
   intuition.
   destruct H1 as [M1 [Typing1 In_M1]].
   destruct H as [M2 [Typing2 In_M2]].
   destruct (Pair_totality M1 M2) as [M12 MPair].
   exists M12.
   split.
   SCase "typing".
     eauto.
   SCase "in M12".
     inversion MPair. subst. firstorder.
Case "nd_typing_app".
   intuition.
   destruct H3 as [M1 [Typing_1 In_M1]].
   destruct H1 as [M2 [Typing_2 In_M2]].
    destruct (App_totality sigma M1 M2) as [M AppM].
   exists M.
   split.
   SCase "typing". eauto.
   SCase "In M".
    inversion AppM.
    subst. 
    assert (In (coerce m1 e1', typ_fun targ tret) Mf) as inToFun.
      inversion H2. firstorder.
    eauto.
Case "nd_typing Proj One".
   intuition.
   destruct H1 as [M [Typing In_M]].
   destruct (Proj_totality sigma M One) as [M1 M1_proj].
   exists M1. 
   split.
   SCase "typing". eauto.
   SCase "In M1". 
     inversion M1_proj. firstorder. subst.
     destruct (H1 _ _ _ _ _ In_M H) as [t' [A1 [A2 A3]]]. 
     intuition. subst. auto.
Case "nd_typing Proj Two".
   intuition.
   destruct H1 as [M [Typing In_M]].
   destruct (Proj_totality sigma M Two) as [M1 M1_proj].
   exists M1. 
   split.
   SCase "typing". eauto.
   SCase "In M1". 
     inversion M1_proj. firstorder. subst.
     destruct (H1 _ _ _ _ _ In_M H) as [t' [A1 [A2 A3]]]. 
     intuition. subst. auto.
Qed.

Lemma open_exp_list_map : forall e t x M, 
  In (e, t) M -> 
  In (open_exp 0 (exp_fvar x) e, t) (open_exp_list 0 (exp_fvar x) M).
intros.
 induction M.
 inversion H.
induction a. rename a into e'. rename b into t'.
destruct (in_inv H). injection H0. intros. subst.
unfold open_exp_list. simpl. left. auto.
unfold open_exp_list. simpl. right. intuition.
Qed.

Hint Resolve open_exp_list_map.

Lemma typing_implies_nd_typing : forall sigma G e M e' t, 
  (ok sigma) -> (ok G) -> 
  (typing sigma G e M) -> 
  (In (e', t) M) -> 
  (nd_typing sigma G e e' t).
Proof.
intros sigma G e M e' t ok_sigma ok_G Typing_e In_M. 
generalize dependent e'. generalize dependent t.
induction Typing_e.
Case "typing var". intros.
  destruct In_M. injection H0. intros. subst. eauto. destruct H0.
Case "typing base". intros.
  destruct In_M. injection H0. intros. subst. eauto. destruct H0.
Case "typing cast". intros.
  rename In_M into In_M'.
  destruct (H _ _ In_M') as [t'_eq In_M]. subst t0.
  firstorder.
Case "typing Abs".
  intros.
  inversion H1. subst.
  destruct (H3 _ _ In_M) as [tret [ebody [e'_eq [t'_eq In_M']]]]. subst.
  eapply (nd_typing_Abs (L `union` dom G)). firstorder.
Case "typing Pair".
  inversion H. subst. intros. 
  destruct (H1 _ _ In_M) as [m1 [m2 [t1 [t2 [e_eq [t_eq [In_M1 In_M2]]]]]]]. 
  subst. firstorder.
Case "typing App".
 intros.
 inversion H.
    subst.
       destruct (H3 _ _ In_M) as [e1' [c [e2' [t1 [t1' [e_eq [In_Mf [In_M2 cgen]]]]]]]]. subst.
    inversion H1. subst.
       destruct (H6 _ _ In_Mf) as [_e1 [_m [_t1 [_t2 [_t' [_e_eq [_t_eq [_cgen _In_M1]]]]]]]].
       subst.
 injection _t_eq; intros; subst. eauto.
Case "typing Proj". 
 induction i.
 SCase "typing Proj One".
 intros.
 inversion H. subst.
     destruct (H2 _ _ In_M) as [c [e1 [t' [t1 [t2 [e_eq [In_M' [cgen [t_eq ig]]]]]]]]]. subst.
     intuition. subst.
  eauto.
 SCase "typing Proj Two". 
 intros.
 inversion H. subst.
     destruct (H2 _ _ In_M) as [c [e1 [t' [t1 [t2 [e_eq [In_M' [cgen [t_eq ig]]]]]]]]]. subst.
     intuition. subst.
  eauto.
Qed.
    
