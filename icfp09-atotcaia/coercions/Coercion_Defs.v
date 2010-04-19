Require Export Metatheory.
Set Undo 100000.

(* ******************************************************************************** *)
(* Language syntax *)
(* ******************************************************************************** *)
Inductive ix : Type :=
| One : ix
| Two : ix.

Inductive typ : Type :=
| typ_base : atom -> typ
| typ_fun : typ -> typ -> typ
| typ_pair : typ -> typ -> typ.

Inductive exp : Type := 
| exp_base : atom -> exp
| exp_bvar : nat -> exp
| exp_fvar : atom -> exp
| exp_cast : exp -> typ -> exp
| exp_lam : typ -> exp -> exp 
| exp_app : exp -> exp -> exp
| exp_pair : exp -> exp -> exp
| exp_proj : ix -> exp -> exp.

Fixpoint open_exp (i : nat) (f : exp) (e : exp) {struct e} : exp :=
  match e with
    | exp_bvar j => if i === j then f else (exp_bvar j)
    | exp_base a => exp_base a
    | exp_fvar x => exp_fvar x
    | exp_cast e1 t => exp_cast (open_exp i f e1) t
    | exp_lam t e1 => exp_lam t (open_exp (S i) f e1)
    | exp_app e1 e2 => exp_app (open_exp i f e1) (open_exp i f e2)
    | exp_pair e1 e2 => exp_pair (open_exp i f e1) (open_exp i f e2)
    | exp_proj n e => exp_proj n (open_exp i f e)
  end.

Notation Gamma := (list (atom * typ)).
Notation Sigma := (list (atom * typ)).
Notation pi := (list typ).
Definition id t := (exp_lam t (exp_bvar 0)).
Definition compose t f g := (exp_lam t (exp_app f (exp_app g (exp_bvar 0)))).
Definition funcompose tfun targ Carg Cret :=
  (exp_lam tfun (exp_lam targ (exp_app Cret (exp_app (exp_bvar 1) (exp_app Carg (exp_bvar 0)))))).
Definition paircompose tfst tsnd C1 C2 :=
  (exp_lam (typ_pair tfst tsnd) 
    (exp_pair 
      (exp_app C1 (exp_proj One (exp_bvar 0)))
      (exp_app C2 (exp_proj Two (exp_bvar 0))))).

Notation "[ x ]" := (x::nil).

(* ******************************************************************************** *)
(* Coercion generation *)
(* ******************************************************************************** *)

Inductive alt : Type :=
| AltSub : alt
| AltNoSub : alt.

Inductive reln : Type :=
| RelPrim : reln
| RelSub : reln.

Inductive coercion : Sigma -> pi -> alt -> typ -> reln -> typ -> exp -> Prop :=
| coercion_Id : 
  forall sigma pi a r t, 
    (coercion sigma pi a t r t (exp_lam t (exp_bvar 0)))
    
| coercion_PrimTrans :
  forall sigma pi a a' r t1 t2 t3 f C, 
    (binds f (typ_fun t1 t2) sigma) -> 
    (~ (In t2 pi)) -> 
    (coercion sigma (t2::pi) a' t2 r t3 C) -> 
    (coercion sigma pi a t1 r t3 (compose t1 C (exp_base f)))

| coercion_FunTrans :
  forall sigma pi t1 t2 t' C' t1' t2' C1 C2,
    (~ (In (typ_fun t1' t2') pi)) -> 
    (coercion sigma [t1'] AltSub t1' RelSub t1  C1) -> 
    (coercion sigma [t2]  AltSub t2  RelSub t2' C2) -> 
    (coercion sigma ((typ_fun t1' t2')::pi) AltNoSub (typ_fun t1' t2') RelSub t' C') -> 
    (coercion sigma pi AltSub (typ_fun t1 t2) RelSub t' 
      (compose (typ_fun t1 t2) C' 
        (funcompose (typ_fun t1 t2) t1' C1 C2)))

| coercion_PairTrans :
  forall sigma pi t1 t2 t' C' t1' t2' C1 C2,
    (~ (In (typ_pair t1' t2') pi)) -> 
    (coercion sigma [t1] AltSub t1 RelSub t1' C1) -> 
    (coercion sigma [t2] AltSub t2 RelSub t2' C2) -> 
    (coercion sigma ((typ_pair t1' t2')::pi) AltNoSub (typ_pair t1' t2') RelSub t' C') -> 
    (coercion sigma pi AltSub (typ_pair t1 t2) RelSub t' 
      (compose (typ_pair t1 t2) C' 
        (paircompose t1 t2 C1 C2)))
.

Definition coerciongen sigma t r t' C := 
  (coercion sigma [t] AltSub t r t' C).

Definition coerce m e : exp := 
  match m with
    | (exp_lam t (exp_bvar 0)) => e
    | _ => (exp_app m e)
  end.


(* ******************************************************************************** *)
(* Non-deterministic formulation of coercion insertion *)
(* ******************************************************************************** *)

Inductive nd_typing : Sigma -> Gamma -> reln -> reln -> exp -> exp -> typ -> Prop :=
| nd_typing_Var :
  forall sigma G d d' x t, 
    (binds x t G) -> 
    (nd_typing sigma G d d' (exp_fvar x) (exp_fvar x) t)
    
| nd_typing_Base : 
  forall sigma G b t d d',
    (binds b t sigma) -> 
    (nd_typing sigma G d d' (exp_base b) (exp_base b) t)

| nd_typing_Cast :
  forall sigma G e e' t d d', 
    (nd_typing sigma G d d' e e' t) -> 
    (nd_typing sigma G d d' (exp_cast e t) e' t)
    
| nd_typing_Abs : 
  forall L sigma G t_x e e' t d d',
    (forall x, x `notin` L -> 
      (nd_typing sigma ([(x,t_x)] ++ G) d d' (open_exp 0 (exp_fvar x) e) (open_exp 0 (exp_fvar x) e') t)) -> 
    (nd_typing sigma G d d' (exp_lam t_x e) (exp_lam t_x e') (typ_fun t_x t))

| nd_typing_Pair : 
  forall sigma G e1 e1' t1 e2 e2' t2 d d', 
    (nd_typing sigma G d d' e1 e1' t1) ->
    (nd_typing sigma G d d' e2 e2' t2) -> 
    (nd_typing sigma G d d' (exp_pair e1 e2) (exp_pair e1' e2') (typ_pair t1 t2))
    
| nd_typing_App :
  forall sigma G e1 e1' t1 e2 e2' t2 targ tret m1 m2 d d',
    (nd_typing sigma G d d' e1 e1' t1) -> 
    (nd_typing sigma G d d' e2 e2' t2) -> 
    (coerciongen sigma t1 d (typ_fun targ tret) m1) -> 
    (coerciongen sigma t2 d' targ m2) -> 
    (nd_typing sigma G d d' (exp_app e1 e2) (exp_app (coerce m1 e1') (coerce m2 e2')) tret)

| nd_typing_Proj_One :
  forall sigma G e e' t t1 t2 m d d', 
    (nd_typing sigma G d d' e e' t) -> 
    (coerciongen sigma t d (typ_pair t1 t2) m) -> 
    (nd_typing sigma G d d' (exp_proj One e) (exp_proj One (coerce m e')) t1)

| nd_typing_Proj_Two :
  forall sigma G e e' t t1 t2 m d d', 
    (nd_typing sigma G d d' e e' t) -> 
    (coerciongen sigma t d (typ_pair t1 t2) m) -> 
    (nd_typing sigma G d d' (exp_proj Two e) (exp_proj Two (coerce m e')) t2)
.

(* ******************************************************************************** *)
(* Non-ambiguity constraints *)
(* ******************************************************************************** *)
Definition WF_uniquepath r sigma := 
  forall a t t' C C' pi, 
    In t pi -> 
    (coercion sigma pi a t r t' C) -> 
    (coercion sigma pi a t r t' C') -> 
    (C = C').

Definition WF_to_uniquefunc r sigma :=
  forall a t t1 t1' t2 t2' C C' pi,
    In t pi ->
    (coercion sigma pi a t r (typ_fun t1 t2) C) ->
    (coercion sigma pi a t r (typ_fun t1' t2') C') ->
    ((C = C') /\ (t1 = t1') /\ (t2 = t2')).

Definition WF_to_uniquepair r sigma :=
  forall a t t1 t1' t2 t2' C C' pi,
    In t pi ->
    (coercion sigma pi a t r (typ_pair t1 t2) C) ->
    (coercion sigma pi a t r (typ_pair t1' t2') C') ->
    ((C = C') /\ (t1 = t1') /\ (t2 = t2')).

Definition WF_from_uniquefunc r sigma :=
  forall t t1 t1' t2 t2' C C',
    (coerciongen sigma (typ_fun t1 t2) r t C) ->
    (coerciongen sigma (typ_fun t1' t2') r t C') ->
    ((C = C') /\ (t1 = t1') /\ (t2 = t2')).

Definition WF_from_uniquepair r sigma :=
  forall t t1 t1' t2 t2' C C',
    (coerciongen sigma (typ_pair t1 t2) r t C) ->
    (coerciongen sigma (typ_pair t1' t2') r t C') ->
    ((C = C') /\ (t1 = t1') /\ (t2 = t2')).

Definition WF sigma i j  :=
  (ok sigma) /\  (WF_to_uniquefunc i sigma) /\ (WF_to_uniquepair i sigma) /\ (WF_uniquepath j sigma).

Definition WF_app d d' sigma :=
  forall t t' t1 t2 t3 t4 m1 m2 m3 m4,
    (coerciongen sigma t1 d (typ_fun t2 t) m1) -> 
    (coerciongen sigma t4 d' t2 m2) -> 
    (coerciongen sigma t1 d (typ_fun t3 t') m3) -> 
    (coerciongen sigma t4 d' t3 m4) -> 
    (t2=t3 /\ t=t').

Definition NAC sigma d d' :=
  (WF_uniquepath d sigma) /\ 
  (WF_uniquepath d' sigma) /\
  (WF_to_uniquepair d sigma) /\ 
  (WF_app d d' sigma).

(* ********************************************************************** *)
(* Some more special tactics *)
(* ********************************************************************** *)
Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  constr:(A `union` B `union` C ).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in
  (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.


Inductive freevars : exp -> atoms -> Prop :=
| FV_bvar :
  forall n, freevars (exp_bvar n) AtomSet.F.empty

| FV_base:
  forall a, freevars (exp_base a) AtomSet.F.empty

| FV_fv:
  forall a, freevars (exp_fvar a) (singleton a)

| FV_lam: 
  forall t e fvs, (freevars e fvs) -> (freevars (exp_lam t e) fvs)

| FV_app:
  forall e1 e2 fvs1 fvs2, 
    (freevars e1 fvs1) -> (freevars e2 fvs2) -> 
    (freevars (exp_app e1 e2) (fvs1 `union` fvs2))

| FV_pair :
  forall e1 e2 fvs1 fvs2, 
    (freevars e1 fvs1) -> (freevars e2 fvs2) -> 
    (freevars (exp_pair e1 e2) (fvs1 `union` fvs2))

| FV_proj :
  forall e i fvs, 
    (freevars e fvs) -> 
    (freevars (exp_proj i e) fvs)

| FV_cast: 
  forall t e fvs, 
    (freevars e fvs) -> 
    (freevars (exp_cast e t) fvs)
.

