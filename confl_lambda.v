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

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof.
assert (not_or: forall (A B: Prop), ~(A \/ B) <-> ~ A /\ ~ B).
{
  unfold not.
  split.
  - intro H.
    split.
    + intro H0.
      destruct H.
      left. 
      assumption.
    + intro H0.
      destruct H.
      right.
      assumption.
  - intros H H0.
    destruct H.
    destruct H0; contradiction.
}
intros x E F.
apply iff_stepl with (~((x \in E) \/ (x \in F))).
- apply not_or.
- split; unfold not; intros; destruct H; apply union_spec in H0; assumption.
Qed.

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


Fixpoint close_rec  (k : nat) (x : var) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_labs t1 => pterm_labs (close_rec (S k) x t1)
  end.

Definition close t x := close_rec 0 x t.
(* end hide *)

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

(* -Os pré-termos dentro da aplicação e abstrações deveriam ser termos 
   -O lemma provavelmente não pode valer para o caso da variável ligada*)
Lemma subst_term: forall t, (forall u n, term t -> {n ~> u} t = t).
Proof.
  intro t; induction t.
  - admit.
  - admit.
  - admit.
  - intros u n Hterm.
Admitted.

Lemma abs_body: forall t1 t2 L, (forall x, x \notin L -> t1^x = t2^x) -> pterm_abs t1 = pterm_abs t2.
Proof.
  intro t1; induction t1.
  - intro t2; induction t2.
    + intros L H.
      unfold open in H.
      Admitted.

Lemma subst_open: forall t u x n,  ({S n ~> u} t) ^ x = {S n ~> (u ^ x)} (t ^ x). 
Proof.
  Admitted.
  
Lemma subst_term': forall t, (forall u n, term t -> {n ~> u} t = t).
Proof.
  assert (Hind := term_ind (fun t => forall u n, term t -> {n ~> u} t = t)).
  intro t; apply Hind.
  - intros x u n Hterm.
    reflexivity.
  - intros t1 t2 Ht1 IHt1 Ht2 IHt2 u n Hterm.
    simpl.
    inversion Hterm; subst.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros L t1 Ht1 IHt1 u n Hterm.
    inversion Hterm; subst.
    simpl.
    apply abs_body with L0.
    intros x H.
    apply H0 in H.
    generalize dependent H.
    rewrite subst_open.
    assert (IHt1' := (IHt1 x)).
    apply IHt1.

        pick_fresh x.
    apply notin_union in Fr.
    destruct Fr.
    apply notin_union in H.
    destruct H.
    apply notin_union in H.
    destruct H.
    apply notin_union in H.
    destruct H.
    apply notin_union in H.
    destruct H.

    
Admitted.
    
Lemma subst_lemma: forall (t1 t2 t3: pterm) (i j:nat), term t3 -> i <> j -> {j ~> t3} ({i ~> t2} t1) = {i ~> {j ~> t3} t2} ({j ~> t3} t1).
Proof.
  intro t1; induction t1.
  - intros t2 t3 i j Ht3 Hij.
    simpl ({i ~> t2} pterm_bvar n).
    destruct (i === n).
    + subst.
      simpl (({j ~> t3} pterm_bvar n)).
      destruct (j === n).
      * symmetry in e; contradiction.
      * replace ({n ~> {j ~> t3} t2} pterm_bvar n) with ({j ~> t3} t2).
        ** reflexivity.
        ** simpl.
           destruct (n === n).
           *** reflexivity.
           *** contradiction.
    + simpl  ({j ~> t3} pterm_bvar n).
      destruct (j === n).
      * rewrite subst_term.
        ** reflexivity.
        ** assumption.
      * simpl.
        destruct (i === n).
        ** contradiction.
        ** reflexivity.
  - Admitted.

(*
Fixpoint lc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_labs t1    => lc_at (S k) t1
  end.

(** Provar equivalência entre lc_at e term/lterm *)

(** term ({k ~> t3} ({i ~> t2} t1)) sse
a expressão ({i ~> t2} t1) pode ter uma ocorrência do índice solto k ou não tem k sse
a expressão t1 pode ter ocorrências dos índices i e/ou k 


term ({k ~> {k ~> t3} t2} ({S k ~> t3} t1)) 

Lemma subst_lemma: forall (t1 t2 t3: pterm) (i k:nat), term t3 -> i <= k -> term ({k ~> t3} ({i ~> t2} t1)) -> term ({k ~> {(k-i) ~> t3} t2} ({S k ~> t3} t1)) -> {k ~> {k ~> t3} t2} ({S k ~> t3} t1) = {k ~> t3} ({i ~> t2} t1). *)

Lemma subst_lemma: forall (t1 t2 t3: pterm) (i k:nat), term t3 -> i <= k -> lc_at (S i) t2 -> lc_at (S k) t1 -> {i ~> {k ~> t3} t2} ({S k ~> t3} t1) = {k ~> t3} ({i ~> t2} t1).
Proof.
  intro t; induction t.
  - intros t2 t3 i k Hterm Hleq Hlt2 Hlt1.
    simpl in Hlt1.
    simpl ({i ~> t2} pterm_bvar n).
    destruct (i === n); subst.
    + assert (n <> S k).
      {
        intro Heq; subst.
        admit.
      }
      replace ({S k ~> t3} pterm_bvar n) with (pterm_bvar n).
      * simpl.
        destruct (n === n).
        ** reflexivity.
        **  contradiction.
      * admit.
    + 
      
(*    
Lemma subst_lemma: forall (t1 t2 t3: pterm) (i k:nat), term t3 -> i <= k -> {i ~> {(k-i) ~> t3} t2} ({S k ~> t3} t1) = {k ~> t3} ({i ~> t2} t1).
Proof.
  intro t1; induction t1.
  - intros t2 t3 i k Ht3 Hleq.
    simpl({i ~> t2} pterm_bvar n).
    destruct(i === n).
    + subst.
      destruct(n === (S k)).
      * subst.
        assert (H := Nat.nle_succ_diag_l k).
        contradiction.
      * replace ({S k ~> t3} pterm_bvar n) with (pterm_bvar n).
        ** simpl.
           destruct (n === n).
           *** simpl.
             admit.
           *** contradiction.
        ** unfold open_rec.
           destruct (S k === n).
           *** symmetry in e.
               contradiction.
           *** reflexivity.
    + simpl ({k ~> t3} pterm_bvar n).
      destruct (k === n).
      * subst.
      *
      
      admit.
  - admit.
  - admit.
  - admit.
  - admit.
   (*
    case i.
    + case k.
      *case n.
       ** simpl.
          reflexivity.
       ** intros n0.
          simpl({0 ~> t2} pterm_bvar (S n0)).
          simpl({0 ~> t3} pterm_bvar (S n0)).
          admit.
      * intros n0.
        simpl. 
    +
    *)
Admitted.                                                                               *)   
 *)

(*
Lemma open_rec_open_rec: forall t1 t2 n m x, {n ~> pterm_fvar x}({m ~> t2} t1) = {m ~> {n ~> pterm_fvar x}t2}({S n ~> pterm_fvar x}t1).
Proof.
  intro t1; induction t1.
  - intros t2 n' m x.
    simpl ({m ~> t2} pterm_bvar n).
    destruct (m === n).
    rewrite e. clear e.
Admitted.
  
Lemma open_rec_open: forall t1 t2 n x, {n ~> pterm_fvar x}(t1 ^^ t2) = ({S n ~> pterm_fvar x}t1) ^^ ({n ~> pterm_fvar x}t2).
Proof.
  intro t; induction t.
  - intros t2 n0 x.
    unfold open.
    case n.
    + reflexivity.
    + intro n1.
      change ({0 ~> t2} pterm_bvar (S n1)) with (pterm_bvar (S n1)).
      case (n0 === n1).
      * intro Heq.
        rewrite Heq.
        admit.
      * intro Hneq.
        admit.
  - intros t2 n0 x.
    reflexivity.
  - intros  t0 n0 x.
    unfold open in *.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - intros t2 n0 x.
    unfold open in *.
    simpl.
    admit.
  - intros t2 no x.
    unfold open in *.
    simpl.
    admit.
Admitted.
 *)

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

(* ? 
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
 *)

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
| reflex: forall a, refltrans red a a
| atleast1: forall a b, red a b -> refltrans red a b
| rtrans: forall a b c, refltrans red a b -> refltrans red b c -> refltrans red a c.

Inductive refltrans' (red: Rel pterm) : Rel pterm :=
| refl: forall a, refltrans' red a a
| rtrans': forall a b c, red a b -> refltrans' red b c -> refltrans' red a c.

Lemma refltrans_equiv: forall (R: Rel pterm) (a b: pterm), refltrans R a b <-> refltrans' R a b.
Proof.
  intros R a b; split.
  - intro H.
    induction H.
    + apply refl.
    + apply rtrans' with b.
      * assumption.
      * apply refl.
    + clear H H0.
      induction IHrefltrans1.
      * assumption.
      * apply rtrans' with b.
        ** assumption.
        ** apply IHIHrefltrans1; assumption.
  - intro H.
    induction H.
    + apply reflex.
    + apply rtrans with b.
      * apply atleast1; assumption.
      * assumption.
Qed.    

Inductive rule_b : Rel pterm  :=
  reg_rule_b : forall (t u:pterm), body t -> term u ->
    rule_b (pterm_app(pterm_abs t) u) (t ^^ u).
Notation "t -->B u" := (contextual_closure rule_b t u) (at level 60).
Notation "t -->>B u" := (refltrans (contextual_closure rule_b) t u) (at level 60).

Inductive rule_lb : Rel pterm  :=
  | reg_rule_bb : forall (t u:pterm), body t -> term u ->
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

(* Precisamos de um lema entre phi e open. *)  
Lemma phi_open_rec_fvar: forall t n x, phi(open_rec n (pterm_fvar x) t) = open_rec n (pterm_fvar x) (phi t).
Proof.  
  intro t; induction t.
  - intros n' x.
    simpl.
    destruct(n' === n).
    + reflexivity.
    + reflexivity.
  - intros n x.
    reflexivity.
  - intros n x.
    change ({n ~> (pterm_fvar x)} pterm_app t1 t2) with (pterm_app ({n ~> (pterm_fvar x)} t1) ({n ~> (pterm_fvar x)} t2)).
    generalize dependent IHt1.
    case t1.
    + intros n0 IHt1.
      simpl (phi (pterm_app (pterm_bvar n0) t2)).
      simpl ( {n ~> pterm_fvar x} pterm_app (pterm_bvar n0) (phi t2)).
      simpl ({n ~> pterm_fvar x} pterm_bvar n0).
      destruct(n === n0); subst.
      * simpl.
        rewrite IHt2.
        reflexivity.
      * simpl.
        rewrite IHt2.
        reflexivity.
    + intros v IHt1.
      simpl.
      f_equal.
      apply IHt2. 
    + intros t11 t12 IHt1.
      simpl ({n ~> pterm_fvar x} pterm_app t11 t12).
      change (phi
    (pterm_app (pterm_app ({n ~> pterm_fvar x} t11) ({n ~> pterm_fvar x} t12))
               ({n ~> pterm_fvar x} t2))) with
    (pterm_app (phi (pterm_app ({n ~> pterm_fvar x} t11) ({n ~> pterm_fvar x} t12)))
               (phi ({n ~> pterm_fvar x} t2))).
      change (phi (pterm_app (pterm_app t11 t12) t2)) with
          (pterm_app (phi (pterm_app t11 t12)) (phi t2)).
      change ({n ~> pterm_fvar x} pterm_app (phi (pterm_app t11 t12)) (phi t2)) with (pterm_app ({n ~> pterm_fvar x}(phi (pterm_app t11 t12))) ({n ~> pterm_fvar x}(phi t2))).
      rewrite IHt2.
      rewrite <- IHt1.
      reflexivity.
    + intros t1' IHt1.
      simpl in *.
      rewrite IHt2.
      rewrite <- IHt1.
      reflexivity.
    + intros t1' IHt1.

      simpl ({n ~> pterm_fvar x} pterm_labs t1').
      simpl in *.
      rewrite IHt2.
      replace ({n ~> pterm_fvar x} (phi t1' ^^ phi t2)) with (phi ({S n ~> pterm_fvar x} t1') ^^ ({n ~> pterm_fvar x} phi t2)).
      * reflexivity.
      * assert (IHt1' := IHt1 n x).
        clear IHt1.
        inversion IHt1'. clear IHt1'.
        rewrite H0.
        rewrite <- open_rec_open.
        reflexivity.
  - intros n x.
    simpl.
    rewrite IHt.
    reflexivity.
  - intros n x.
    simpl.
    rewrite IHt.
    reflexivity.
Qed.

Corollary phi_open: forall t x, phi(t^x) = (phi t)^x.
Proof.
  intros t x.
  unfold open.
  apply phi_open_rec.
Qed.

Lemma phi_term: forall t, lterm t -> term (phi t).
Proof.
  intros t Hlterm.
  induction Hlterm.
  - simpl.
    apply term_var. 
  - generalize dependent t2.
    induction t1.
    + simpl in *.
      inversion Hlterm1.
    + simpl in *.
      intros t2 Hlterm2 Hterm2.
      apply term_app.
        * apply term_var.
        * assumption. 
    + intros t2 Hlterm2 Hterm2.
      admit.
    + intros t2 Hlterm2 Hterm2.
      simpl.
      apply term_app.
        * simpl in IHHlterm1.
          assumption.
        * assumption. 
    + intros t2 Hlterm2 Hterm2.
      clear IHt1.
      simpl in *.
      inversion Hlterm1.
  - simpl.    
    unfold open.
    admit.
  - simpl.
    apply term_abs with L.
    intros x HL.
    rewrite <- phi_open.
    apply H0; assumption.
Admitted.

Lemma term_fvar_to_term: forall t1 t2 t3 x, term (phi (pterm_app t1 t2)^x) -> term t3 -> term (phi (pterm_app t1 t2)^^t3). 
Proof.
Admitted.  

Lemma term_phi_open: forall t1 t2 x L,  x \notin L -> term (phi (t1 ^ x)) -> term (phi t2) -> term (phi t1 ^^ phi t2).
Proof.
  intro t; induction t.
  - intros t2 x L HL Hterm1 Hterm2.
    unfold open in *.
    generalize dependent n.
    intro n; case n.
    + intro H.
      assumption.
    + intros n'; simpl.
      intro H; inversion H.
  - intros t3 x L HL.
    intros Hfvphi Ht3.
    simpl.
    assumption.
  - intros t2' x L HL Hterm1 Hterm2.
    unfold open in *.
    rewrite phi_open_rec in Hterm1.
    apply term_fvar_to_term with x; assumption.
  - intros t2 x L HL Hterm1 Hterm2.
    assert(teste := IHt t2 x L HL).
    admit. (* Gabriel *)
Admitted.
  (*
  intro t; induction t.
  - intro H; inversion H.
  - intro H; assumption.
  - intro H; inversion H; subst.
    generalize dependent t1.
    intro t1; case t1.
    + intros n H1 H2 H4.
      inversion H4.
    + intros n H1 H2 H4. simpl.
      apply IHt2 in H3.
      apply term_app; assumption.
    + intros t3 t4 H1 H2 H4.
      apply IHt2 in H3.
      change (phi (pterm_app (pterm_app t3 t4) t2)) with (pterm_app (phi(pterm_app t3 t4)) (phi t2)).
      apply H1 in H4.
      apply term_app; assumption.
    + intros t3 H1 H2 H4.
      apply IHt2 in H3.
      simpl.
      apply H1 in H4.
      apply term_app; assumption.
    + intros t3 H1 H2 H4.
      simpl.
      apply IHt2 in H3.
      unfold open.
      admit. (* work with lc_at *)
  - admit.
  - Admitted. *)

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

Lemma phi_subst_rec: forall (M N: pterm) (k: nat), term N -> phi ({k ~> N} M) = {k ~> (phi N)}(phi M).
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
    generalize dependent M1. 
    intro M1.
    case M1.
    + intros M1' IHM1.
      change (phi (pterm_app (pterm_bvar M1') M2)) with  (pterm_app (phi(pterm_bvar M1')) (phi M2)).
      change ( {k ~> phi N} pterm_app (phi (pterm_bvar M1')) (phi M2)) with
          ( pterm_app ( {k ~> phi N}(phi (pterm_bvar M1'))) ( {k ~> phi N}(phi M2))).
      assert( IH' := IHM1 N k).
      change ({k ~> N} pterm_app (pterm_bvar M1') M2) with (pterm_app ({k ~> N}(pterm_bvar M1')) ({k ~> N}M2)).
      admit. (* works if N is not a labeled lambda. TODO: add this condition. *)
    + intros N0 k0.
      simpl in *.
      f_equal.
  (*     apply IHM2. *)
  (*   + intros N0 k0 IHM1. *)
  (*     change (phi (pterm_app (pterm_app N0 k0) M2)) with (pterm_app (phi (pterm_app N0 k0)) (phi M2)). *)
  (*     change ({k ~> phi N} pterm_app (phi (pterm_app N0 k0)) (phi M2)) with (pterm_app ({k ~> phi N} (phi (pterm_app N0 k0)))({k ~> phi N} (phi M2))). *)
  (*     rewrite <- IHM1. *)
  (*     rewrite <- IHM2. *)
  (*     change ({k ~> N} pterm_app (pterm_app N0 k0) M2) with (pterm_app ({k ~> N}(pterm_app N0 k0)) ({k ~> N} M2)). *)
  (*     change (phi (pterm_app ({k ~> N} pterm_app N0 k0) ({k ~> N} M2))) with *)
  (*         (pterm_app (phi ({k ~> N} pterm_app N0 k0)) (phi ({k ~> N} M2))). *)
  (*     reflexivity. *)
  (*   + intros N0 k0. *)
  (*     simpl. *)
  (*     f_equal. *)
  (*      * apply k0. *)
  (*      * apply IHM2. *)
  (*   + intros M1' IH. *)
  (*     simpl in *. *)
  (*     rewrite IHM2. *)
  (*     assert (IH' := IH N k). *)
  (*     inversion IH'. *)
  (*     rewrite H0. *)
  (*     unfold open. *)
  (*     apply subst_lemma. *)

  (*     apply Peano.le_0_n. *)
  (* - intros N k. *)
  (*   simpl. *)
  (*   f_equal. *)
  (*   apply IHM. *)
  (* - intros N k. *)
  (*   simpl. *)
  (*   f_equal. *)
  (*   apply IHM. *)
Admitted.    

Corollary phi_subst: forall M N, phi (M ^^ N) = (phi M) ^^ (phi N). 
Proof.
  Admitted.

Lemma phi_prop: forall M N : pterm, lterm M -> lterm N -> (M -->>lB N) -> (phi M) -->>B (phi N).
Proof.
  intros M N Hterm1 Hterm2 H.
  induction H.
  -
  -
  -
    
  
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
