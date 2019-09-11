Definition var := nat.

Require Import Arith MSetList Setoid.

Declare Module Var_as_OT : UsualOrderedType
  with Definition t := var.
Module Import VarSet := MSetList.Make Var_as_OT.

Definition vars := VarSet.t.

Notation "{}" := (VarSet.empty).
Notation "{{ x }}" := (VarSet.singleton x).
Notation "s [=] t " := (VarSet.Equal s t) (at level 70, no associativity). 
Notation "E \u F" := (VarSet.union E F)  (at level 68, left associativity).
Notation "x \in E" := (VarSet.In x E) (at level 69).
Notation "x \notin E" := (~ VarSet.In x E) (at level 69).
Notation "E << F" := (VarSet.Subset E F) (at level 70, no associativity).
Notation "E \rem F" := (VarSet.remove F E) (at level 70).

Lemma eq_var_dec : forall x y : var, {x = y} + {x <> y}.
Proof. exact eq_nat_dec. Qed.

Notation "x == y" := (eq_var_dec x y) (at level 67).
Notation "i === j" := (Peano_dec.eq_nat_dec i j) (at level 67).

(** Pre-terms are defined according to the following grammar: *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_labs  : pterm -> pterm.

(*
Inductive ctx (t:pterm) :=
| ctx_empty: t.
???
 *)

Fixpoint fv (t : pterm) : vars :=
  match t with
  | pterm_bvar i    => {}
  | pterm_fvar x    => {{x}}
  | pterm_app t1 t2 => (fv t1) \u (fv t2)
  | pterm_abs t1    => (fv t1)
  | pterm_labs t1    => (fv t1)
  end.

Fixpoint bv (t : pterm) : vars :=
  match t with
  | pterm_bvar i    => {{i}}
  | pterm_fvar x    => {}
  | pterm_app t1 t2 => (bv t1) \u (bv t2)
  | pterm_abs t1    => (bv t1)
  | pterm_labs t1    => (bv t1)
  end.

Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | {} => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u V)
      end
    | _ => V
    end in
  let L := gather {} in eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let D := gather_vars_with (fun x : pterm => fv x) in
  constr:(A \u B \u D).

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | ?E1 \u ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | {}  => Acc
     | ?E1 => match Acc with
              | {} => E1
              | _ => constr:(Acc \u E1)
              end
     end
  in go {} V.

Require Import List Omega.
Open Scope list_scope.

Lemma max_lt_l :
  forall (x y z : nat), x <= y -> x <= max y z.
Proof.
  induction x; auto with arith.
  induction y; induction z; simpl; auto with arith.
Qed.

Lemma finite_nat_list_max : forall (l : list nat),
  { n : nat | forall x, In x l -> x <= n }.
Proof.
  induction l as [ | l ls IHl ].
  - exists 0; intros x H; inversion H.
  - inversion IHl as [x H]; clear IHl.
    exists (max x l).
    intros x' Hin.
    inversion Hin; subst.
    + auto with arith.
    + assert (x' <= x); auto using max_lt_l.
Qed.      

Lemma finite_nat_list_max' : forall (l : list nat),
  { n : nat | ~ In n l }.
Proof.
  intros l. case (finite_nat_list_max l); intros x H.
  exists (S x). intros J. assert (K := H _ J); omega.
Qed.

Definition var_gen (L : vars) : var :=
  proj1_sig (finite_nat_list_max' (elements L)).

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  unfold var_gen. intros E.
  destruct (finite_nat_list_max' (elements E)) as [n pf].
  simpl. intros a. 
  destruct pf.
  apply elements_spec1 in a.
  rewrite InA_alt in a.
  destruct a as [y [H1 H2]].
  subst; assumption.
Qed.
  
Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof.
  intros L. exists (var_gen L). apply var_gen_spec.
Qed.

Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_fresh L) as [Y Fr]).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if k === i then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1)
  | pterm_labs t1    => pterm_labs (open_rec (S k) u t1)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67). 
Notation "t ^ x" := (open t (pterm_fvar x)).   

(** Check how close operation is being used in the formalization. 
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  end.

Definition close t x := close_rec 0 x t. *)
(* end hide *)
(** ES terms are expressions without dangling deBruijn indexes. *)

Inductive term : pterm -> Prop :=
  | term_var : forall x,
      term (pterm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (pterm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (pterm_abs t1).

Inductive lterm : pterm -> Prop :=
  | term_lvar : forall x,
      lterm (pterm_fvar x)
  | term_lapp : forall t1 t2,
      lterm t1 -> 
      lterm t2 -> 
      lterm (pterm_app t1 t2)
  | term_lrdx : forall L t1 t2,
      (forall x, x \notin L -> lterm (t1 ^ x)) ->
      lterm t2 -> 
      lterm (pterm_app (pterm_labs t1) t2)
  | term_labs : forall L t1,
      (forall x, x \notin L -> lterm (t1 ^ x)) ->
      lterm (pterm_abs t1).

Hint Constructors lterm term.

Definition Rel (A:Type) := A -> A -> Prop.

Inductive contextual_closure (R: Rel pterm) : Rel pterm :=
  | redex : forall t s, R t s -> contextual_closure R t s
  | app_left : forall t t' u, contextual_closure R t t' -> term u ->
	  		      contextual_closure R (pterm_app t u) (pterm_app t' u)
  | app_right : forall t u u', contextual_closure R u u' -> term t ->
	  		       contextual_closure R (pterm_app t u) (pterm_app t u')
  | abs_in : forall t t' L, (forall x, x \notin L -> contextual_closure R (t^x) (t'^x)) ->
                               contextual_closure R (pterm_abs t) (pterm_abs t').

Inductive lcontextual_closure (R: Rel pterm) : Rel pterm :=
  | lredex : forall t s, R t s -> lcontextual_closure R t s
  | lapp_left : forall t t' u, lcontextual_closure R t t' -> lterm u ->
	  		      lcontextual_closure R (pterm_app t u) (pterm_app t' u)
  | lapp_right : forall t u u', lcontextual_closure R u u' -> lterm t ->
	  		       lcontextual_closure R (pterm_app t u) (pterm_app t u')
  | labs_in : forall t t' L, (forall x, x \notin L -> contextual_closure R (t^x) (t'^x)) ->
                               lcontextual_closure R (pterm_abs t) (pterm_abs t')
  | l_abs_in : forall t t' L, (forall x, x \notin L -> lcontextual_closure R (t^x) (t'^x)) ->
                               lcontextual_closure R (pterm_labs t) (pterm_labs t').

Definition body t := exists L, forall x, x \notin L -> term (t ^ x).
Definition lbody t := exists L, forall x, x \notin L -> lterm (t ^ x).


Fixpoint erase (t:pterm) : pterm :=
  match t with
  | pterm_app t1 t2 => pterm_app (erase t1) (erase t2)
  | pterm_abs t1 => pterm_abs (erase t1)
  | pterm_labs t1 => pterm_abs (erase t1)
  | _ => t
  end.

Fixpoint unerase (t:pterm) : pterm :=
  match t with
  | pterm_app t1 t2 =>
    match t1 with
    | pterm_abs t1 => pterm_app (pterm_labs (unerase t1)) (unerase t2)
    | _ => pterm_app (unerase t1) (unerase t2)
    end
  | pterm_abs t1 => pterm_abs (unerase t1)
  | _ => t
  end.

Lemma erase_idemp: forall a, erase (erase a) = erase a.
Proof.
  induction a.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  - simpl.
    rewrite IHa; reflexivity.
  - simpl.
    rewrite IHa; reflexivity.
Qed.
    
Inductive refltrans (red: Rel pterm) : Rel pterm :=
| reflex: forall a b, erase a = erase b -> refltrans red a b
| atleast1: forall a b, red a b -> refltrans red a b
| rtrans: forall a b c, refltrans red a b -> refltrans red b c -> refltrans red a c.

Inductive rule_b : Rel pterm  :=
  reg_rule_b : forall (t u:pterm),
    body t -> term u ->
    rule_b (pterm_app(pterm_abs t) u) (t ^^ u).
Notation "t -->B u" := (contextual_closure rule_b t u) (at level 60).
Notation "t -->>B u" := (refltrans (contextual_closure rule_b) t u) (at level 60).

Inductive rule_lb : Rel pterm  :=
  | reg_rule_bb : forall (t u:pterm),
    body t -> term u ->
    rule_lb (pterm_app(pterm_abs t) u) (t ^^ u)
  | reg_rule_lb : forall (t u:pterm),
    body t -> term u ->
    rule_lb (pterm_app(pterm_labs t) u) (t ^^ u).
Notation "t -->lB u" := (lcontextual_closure rule_lb t u) (at level 60).
Notation "t -->>lB u" := (refltrans (lcontextual_closure rule_lb) t u) (at level 60).

Fixpoint phi (t:pterm) : pterm :=
  match t with
  | pterm_app t1 t2 => match t1 with
                      | pterm_labs t1' => (phi t1') ^^ (phi t2)
                      | _ => pterm_app (phi t1) (phi t2)
                      end
  | pterm_abs t1 => pterm_abs (phi t1)
  | pterm_labs t1 => pterm_labs (phi t1)
  | _ => t
  end.


(*
Lemma lt_preserv_str1 : forall M x, lterm M -> M = (pterm_fvar x) -> erase M = (pterm_fvar x).
Proof.
  intros M x H HM.
  rewrite HM.
  reflexivity.
Qed.    

Lemma lt_preserv_str2 : forall M M1 M2, lterm M -> M = (pterm_app M1 M2) -> erase M = (pterm_app (erase M1) (erase M2)).
Proof.
  intros M M1 M2 H HM.
  rewrite HM.
  reflexivity.
Qed.    

Lemma lt_preserv_str3 : forall M M', lterm M -> M = (pterm_abs M') -> erase M = (pterm_abs (erase M')). 
Proof.
  intros M M' H HM.
  rewrite HM.
  reflexivity.
Qed.    

Lemma lt_preserv_str4 : forall M M' N', lterm M -> M = pterm_app (pterm_labs M') N' -> erase M = pterm_app (pterm_abs (erase M')) (erase N'). 
Proof.
  intros M M' N' H HM.
  rewrite HM.
  reflexivity.
Qed.    
 *)

Lemma lterm_preserves_fvar : forall M x, erase M = (pterm_fvar x) -> M = (pterm_fvar x).
Proof.
  induction M.
  - intros x H.
    simpl in H.
    exact H.
  - intros x H.
    exact H.
  - intros x H.
    simpl in H.
    inversion H.
  - intros x H.
    simpl in H.
    inversion H.
  - intros x H.
    simpl in H.
    inversion H.
Qed.

Lemma lterm_preserves_bvar : forall M n, erase M = (pterm_bvar n) -> M = (pterm_bvar n).
Proof.
  Admitted.

Lemma lterm_preserves_app : forall M N L, erase M = (pterm_app N L) -> exists N' L', M = (pterm_app N' L').
Proof.
(*
  exists (erase N).
  exists (erase L). *)
  Admitted.

Lemma lterm_preserves_abs : forall M N, erase M = (pterm_abs N) -> exists N', M = (pterm_abs N') \/ M = (pterm_labs N').
Proof.
Admitted.

Lemma open_rec_preserves_labs: forall t u k, (open_rec k u (pterm_labs t)) = (pterm_labs (open_rec (S k) u t)).
Proof.
  intros t u k .
  reflexivity.
Qed.
  
Lemma erase_open_rec : forall (M N: pterm) (k : nat), erase ({k ~> N} M) = {k ~> (erase N)} (erase M).
Proof.
  induction M.
  - intros N K.
    simpl.
    destruct (K === n).
    + reflexivity.
    + reflexivity.
  - intros N k. 
    reflexivity.
  - intros N k.
    simpl.
    f_equal.
    + apply IHM1.
    + apply IHM2.
  - intros N k.
    simpl.
    f_equal.
    apply IHM.
  - intros N k.
    simpl.
    f_equal.
    apply IHM.
Qed.

Corollary erase_open : forall M N: pterm, erase (M ^^ N) = (erase M) ^^ (erase N).
Proof.
  unfold open.
  intros M N.
  apply  erase_open_rec.
Qed.

Lemma subst_lemma: forall (M1 M2 M3: pterm) (i k:nat), i <= k -> {i ~> {k ~> M3} M2} ({S k ~> M3} M1) = {k ~> M3} ({i ~> M2} M1).
Proof.
  induction M1.
Admitted.                                                                                  

Lemma phi_subst_rec: forall (M N: pterm) (k: nat), phi ({k ~> N} M) = {k ~> (phi N)}(phi M).
Proof.
  induction M.
  - intros N k.
    simpl.
    destruct (k === n).
    + reflexivity.
    + reflexivity.
  - intros N k.
    simpl.
    reflexivity.
  - intros N k.
    generalize dependent M1. (* duvida no significado *)
    intro M1.
    case M1.
    + intros M1' IHM1.
      change (phi (pterm_app (pterm_bvar M1') M2)) with  (pterm_app (phi(pterm_bvar M1')) (phi M2)).
      change ( {k ~> phi N} pterm_app (phi (pterm_bvar M1')) (phi M2)) with
          ( pterm_app ( {k ~> phi N}(phi (pterm_bvar M1'))) ( {k ~> phi N}(phi M2))).
      assert( IH' := IHM1 N k).
      change ({k ~> N} pterm_app (pterm_bvar M1') M2) with (pterm_app ({k ~> N}(pterm_bvar M1')) ({k ~> N}M2)).
      
      change (phi (pterm_app ({k ~> N} pterm_bvar M1') ({k ~> N} M2))) with  (pterm_app (phi({k ~> N} pterm_bvar M1')) (phi ({k ~> N} M2))).
    + admit.
    + admit.
    + admit.
    + intros M1' IH.
      simpl in *.
      rewrite IHM2.
      assert (IH' := IH N k).
      inversion IH'.
      rewrite H0.
      unfold open.
      apply subst_lemma.
      apply Peano.le_0_n.
  - admit.
  - admit.    
Admitted.    

Corollary phi_subst: forall M N, phi (M ^^ N) = (phi M) ^^ (phi N). 
Proof.
  Admitted.

(*                                       
Lemma erase_prop : forall M N M' N': pterm, lterm M -> lterm N -> (M -->lB N) -> erase M = M' -> erase N = N' ->  (M' -->B N').
Proof.
  intros M N M' N' HM HN Hred HerM HerN.
  generalize dependent N'.
  generalize dependent M'.
  induction Hred.
  - induction H.
    + intros M' HerM' N' HerN'.
      simpl in HerM'.
      rewrite <- HerM'.
      rewrite erase_open in HerN'.
      rewrite <- HerN'.
      apply redex.
      apply reg_rule_b.
      * admit.
      * admit.
    + admit.    
  - admit.
  - admit.
  - admit.
  - Admitted.
 *)

Lemma erase_prop_str: forall M' M N , pterm_app (pterm_abs M) N = erase M' -> exists u v, erase u = M -> erase v = N -> (M' = pterm_app (pterm_labs u) v) \/ (M' = pterm_app (pterm_abs u) v).
Proof.
Admitted.

Lemma erase_prop1 : forall M N: pterm, term M -> term N -> (M -->B N) -> forall M' N', (erase M' = M) /\ (erase N' = N) ->  (M' -->lB N').
Proof.
  intros M N HtM HtN Hred.
  
  induction Hred.
  - inversion H; subst.
    apply erase_prop_str in H2.
    destruct H2 as [u0].
    destruct H2 as [v].
    Admitted.
   (* rewrite erase_idemp in H.
    rewrite erase_idemp in H.
    assumption.
  - apply atleast1.
    admit.
  - apply IHHred1. (* ajustar *)
    + assumption.
    + admit. (* ok *)
    + assumption.
    + Admitted.*)

Lemma erase_prop : forall M N M' N': pterm, term M -> term N -> (M -->>B N) -> erase M' = M -> erase N' = N ->  (M' -->>lB N').
Proof.
  intros M N M' N' HtM HtN Hred HeM HeN.
  induction Hred.
  - apply reflex.
    subst.
    rewrite erase_idemp in H.
    rewrite erase_idemp in H.
    assumption.
  - apply atleast1.
    admit.
  - apply IHHred1. (* ajustar *)
    + assumption.
    + admit. (* ok *)
    + assumption.
    + Admitted.
