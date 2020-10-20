(* begin hide *)
Definition var := nat.

Require Import Arith MSetList Setoid.

Set Nested Proofs Allowed.
    
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
(* end hide *)

(** * Locally Nameless Notation *)

(*é
necessário definir o que é uma variável livre e uma variável ligada?*)

(** A notação de nomes locais é definida de forma a trabalhar com index's ligados à abstrações
para representar variáveis ligadas, e variáveis nomeadas para representar variáveis livres. Dessa
forma podemos ter um conjunto de símbolos nesta notação que não sejam válidos semanticamente. 
Vamos exemplificar: 

Dada a abstração $\lambda.0$ sabemos que o index 0 representa a variável ligada à abstração
que apresentamos. O index 0 neste caso indica que existem 0 passos para em uma aplicação
substituir a variável ligada que o mesmo representa, estando esse index portanto ligado
diretamente à abstração apresentada, e sendo dessa maneira válido semanticamento. Porém,
sintaticamente o index pode ser um valor iteiro k qualquer. Assim, por exemplo, ao 
fazermos $\lambda.1$, estamos construindo semanticamente uma relação que não possui 
significado válido. Queremos representar variáveis ligadas por meio de index's e neste caso o 
index 1 não está ligado à nenhuma abstração, portanto não representa uma variável ligada
e não é válido para nossa representação.*)

(** Assim podemos definir o conceito de pré-termo como sendo: Todo conjunto de símbolos sintaticamente
válidos, que ainda não temos certeza acerca da validade semântica. Matematicamente os pré-termos 
são definidos de acordo com a seguinte gramática: *)

Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_labs  : pterm -> pterm.

(** Um pré-termo é um termo do cálculo lambda que possui em si indexs de de Bruijin que não foram
substituídos. (esta definição está correta?)

Definição alternativa:

Um pré-termo é um conjunto de símbolos do cálculo lambda que operam conjuntamente e ainda
não foram verificados como totalmente fechados.*)

(*
Inductive ctx (t:pterm) :=
| ctx_empty: t.
???
 *)
(* begin hide *)
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
(* end hide *)

(** A definição da operação "variable opening", ou seja, abertura de variáveis é dada abaixo:*)

Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if k === i then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1)
  | pterm_labs t1    => pterm_labs (open_rec (S k) u t1)
  end.

(** Esta operação é responsável por substituir todos os índices "k", por uma variável com
nome qualquer. Por exemplo, digamos que tenhamos o pré-termo $\lambda.0 y$, assim, ao aplicar
a operação $ {0 ~> x} \lambda.0 y$ teremos o seguinte resultado: $\lambda.x y$.*)


(** Com isso, a operação de abertura recursiva apenas para index's 0 é definida especialmente 
como "open", onde u é o nome de uma variável qualquer e t é um pré-termo ,logo abaixo:*)

Definition open t u := open_rec 0 u t.

(** Esta definição será extremamente útil nas provas mais abaixo, devido à maior facilidade com relação
à trabalhar com qualquer index k, e para garantir que estamos trabalhando com termos válidos.*)

(** De qualquer forma, a operação como explicada mais acima, onde k é o index de De Bruijin,
u o nome de uma variável qualquer e t o pré-termo que será aberto recursivamente no index k é 
definida como se segue:*)

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(*não me recordo no momento a utilidade das notações abaixo*)

(** Notação para representar a abertura de um termo, substituindo as variáveis ligadas
por qualquer tipo de pré-termo.*)
Notation "t ^^ u" := (open t u) (at level 67). 

(** Notação para representar abertura de um pré-termo utilizando uma variável livre
x:*)
Notation "t ^ x" := (open t (pterm_fvar x)).   

(* begin hide *)
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

(** A definição de termo é dada logo abaixo:*)

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

(** Um termo é válido na notação de nomes locais, quando este termo é um termo fechado. 
Para ser um termo fechado, seguimos uma definição recursiva, onde toda variável livre, e portanto
nomeada é fechada, toda aplicação é fechada, se seus dois termos internos são fechados, e toda
abstração é fechada, se todos os termos que fazem parte da mesma também são fechados. Veja que esta é
exatamente a definição que temos logo acima. Podemos deixar o entendimento mais fácil com a seguinte
definição: Um termo é um pré-termo sem nenhuma variável ligada inválida, ou seja, nenhum index não ligado
à uma abstração de alguma maneira.*)

(** Dessa forma também é interessante definir o conceito de corpo, como sendo todo pré-termo
que após uma abertura no index 0, por uma variável nomeada livre x, torna-se um termo fechado.
A definição está logo abaixo:*)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

(** Perceba que a definição de body foi utilizada na definição recursiva de termo, para
representar as abtrações válidas semanticamente, segundo os conceitos aqui já apresentados.*)

(*
Definition lterm t := term t \/ 

Inductive lterm : pterm -> Prop :=
  | lterm_term : forall t,
      term t -> lterm t
  | lterm_labs : forall L t1,
      (forall x, x \notin L -> lterm (t1 ^ x)) ->
      lterm (pterm_labs t1). *)

(** Para realizar a prova da confluência é necessária a definição de um termo marcado. Um
termo marcado contém exatamente as mesmas propriedades de um termo, exceto que, pode possuir
abstrações marcadas. Abstrações marcadas são aquelas que estão postas em uma aplicação válida,
aonde pode ser aplicada uma B-redução. Abstrações que não fazem parte de uma aplicação, não podem ser 
abstrações marcadas. Podemos ver essa definição em termos recursivos logo abaixo:*)

Inductive lterm : pterm -> Prop :=
  | lterm_var : forall x,
      lterm (pterm_fvar x)
  | lterm_app : forall t1 t2,
      lterm t1 -> 
      lterm t2 -> 
      lterm (pterm_app t1 t2)
  | lterm_abs : forall L t1,
      (forall x, x \notin L -> lterm (t1 ^ x)) ->
      lterm (pterm_abs t1)
  | lterm_labs : forall L t1 t2,
      (forall x, x \notin L -> lterm (t1 ^ x)) ->
      lterm t2 ->
      lterm (pterm_app (pterm_labs t1) t2).

(** Assim, também é possível definir o corpo marcado, como sendo o pré-termo que possui dentro de 
si uma abstração marcada, aonde após uma abertura recursiva do index 0 com uma variável nomeada 
livre qualquer x, torna-se um termo marcado:*)

Definition lbody t :=
  exists L, forall x, x \notin L -> lterm (t ^ x).

Hint Constructors lterm term.

(* This claim is false! because

Lemma lterm_implies_term: forall t, lterm t -> term t.
Proof.
  intros t Hlterm.
  induction Hlterm.
  - apply term_var; assumption.
  - apply term_app; assumption.
  - apply term_abs with L; assumption.
  - apply term_app.
    + admit.
    + assumption.
Admitted. *)

(* a regra abaixo foi utilizada?*)

(** * Definições técnicas e explanação teórica *)

(** Para auxiliar nas provas são necessárias algumas definições no assistente de provas. Existem casos em que é melhor
seguir uma prova por indução na estrutura, nestes casos, o assistente consegue lidar bem com seus pŕoprios comandos. No entanto,
quando precisamos trabalhar com provas no tamanho dos termos, muitas vezes são necessárias definições para contar o tamanho do
tipo que estamos lidando. E posteriormente, essas definições são utilizadas para definir induções no tamanho específicas para o 
domínio em que estamos trabalhando. Não vamos apresentar estas definições neste trabalho, por serem muito técnicas e poderem
ser facilmente encontradas em outros trabalhos da literatura (possivelmente citar trabalhos aqui). *)

(** No trabalho de \cite{Chargerout} (concertar citação) e na notação de nomes locais é necessária a definição de operações de
abertura e fechamento dos termos. As operações de abertura e fechamento manipulam os index's e nomes, e têm como objetivo controlar
e tornar possível a decisão de se um termo é ou não fechado, ou seja, possui uma sintaxe válida. Não iremos mostrar essas definições
neste trabalho, pois as mesmas podem ser encontradas no próprio trabalho de \cite{Chargerout} (concertar citação), mas estas definições
foram utilizadas e exploradas neste trabalho. *)

(* begin hide *)
Fixpoint pterm_size (t : pterm) : nat :=
 match t with
 | pterm_bvar i    => 1
 | pterm_fvar x    => 1
 | pterm_app t1 t2 => (pterm_size t1) + (pterm_size t2)
 | pterm_abs t1    => 1 + (pterm_size t1)
 | pterm_labs t1   => 1 + (pterm_size t1)
 end.

Lemma pterm_size_gt_0: forall t, pterm_size t > 0.
Proof.
  intro t; induction t.
  - simpl.
    auto.
  - simpl.
    auto.
  - simpl.
    apply Nat.add_pos_r; assumption.
  - simpl.
    auto.
  - simpl.
    auto.
Qed.

Lemma pterm_size_open_rec: forall t n x, pterm_size t = pterm_size (open_rec n (pterm_fvar x) t).
Proof.
  intro t; induction t.
  - intros n0 x.
    simpl.
    destruct(n0 === n); reflexivity.
  - intros n x.
    reflexivity.
  - intros n x.
    simpl.
    rewrite <- IHt1.
    rewrite <- IHt2.
    reflexivity.
  - intros n x.
    simpl.
    rewrite <- IHt.
    reflexivity.
  - intros n x.
    simpl.
    rewrite <- IHt.
    reflexivity.
Qed.

(* begin hide *)

Lemma strong_induction :
 forall (P: nat -> Prop),
   (forall n, (forall m, m < n -> P m) -> P n) ->
   (forall n, P n).
Proof.
  intros P H.
  cut (forall n m, m < n -> P m).
  - intros H' n.
    apply H.
    apply H'.
  - induction n.
    + intros m H'.
      inversion H'.
    + intros m Hlt.
      apply H.
      intros m' Htl.
      apply IHn.
      apply lt_n_Sm_le in Hlt.
      apply Nat.lt_le_trans with m; assumption.
Qed.

Lemma pterm_size_induction :
 forall P : pterm -> Prop,
 (forall n, P (pterm_bvar n)) ->
 (forall x, P (pterm_fvar x)) ->
 (forall t1 t2, P t1 -> P t2 -> P (pterm_app t1 t2)) ->
 (forall t1,
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (pterm_abs t1)) ->
 (forall t1,
    (forall t2 x, x \notin fv t2 -> pterm_size t2 = pterm_size t1 ->
    P (t2 ^ x)) -> P (pterm_labs t1)) ->
 (forall t, P t).
Proof.
  intros P h1 h2 h3 h4 h5 t.
  remember (pterm_size t) as n.
  generalize dependent t.
  induction n using strong_induction.
  intro t; destruct t.
  - intro Hsize.
    apply h1.
  - intro Hsize.
    apply h2.
  - simpl.
    intro Hsize.
    apply h3.
    + apply H with (pterm_size t1).
      * rewrite Hsize.
        assert (Ht2: pterm_size t2 > 0).
        {
          apply pterm_size_gt_0.
        }
        rewrite Nat.add_comm.
        apply Nat.lt_add_pos_l.
        assumption.
      * reflexivity.
    + apply H with (pterm_size t2).
      * rewrite Hsize.
        assert (Ht2: pterm_size t1 > 0).
        {
          apply pterm_size_gt_0.
        }
        apply Nat.lt_add_pos_l.
        apply Ht2.
      * reflexivity.
  - simpl.
    intro Hsize.
    apply h4.
    intros t2 x Hfv Hequals.
    apply H with (pterm_size t0).
    rewrite Hsize.
    apply Nat.lt_succ_diag_r.
    assert (Hopen: pterm_size t2 = pterm_size (open_rec 0 (pterm_fvar x) t2)).
    {
      apply pterm_size_open_rec.
    }
    unfold open.
    rewrite <- Hopen.
    symmetry; assumption.
  - simpl.
    intro Hsize.
    apply h5.
    intros t2 x Hfv Hequals.
    apply H with (pterm_size t0).
    rewrite Hsize.
    apply Nat.lt_succ_diag_r.
    assert (Hopen: pterm_size t2 = pterm_size (open_rec 0 (pterm_fvar x) t2)).
    {
      apply pterm_size_open_rec.
    }
    unfold open.
    rewrite <- Hopen.
    symmetry; assumption.
Qed.
(* end hide *)

(** Existe outra maneira de saber se um pré-termo é localmente fechado. ALém do uso do open, 
podemos definir um tipo recursivo chamado "lc_at". A ideia é trabalhar com os index's de modo
a verificar se todos possuem ligação com uma abstrção, e caso sim, o termo será um termo fechado.
Ser um termo fechado, como já dito, significa ser um termo válido para o $\lambda$-cálculo. A comparação
realizada para os index-s refere-se a se estes são menores do que um valor k, ligado ao número de 
abstrações. *)

(** Para um termo ser realmente localmente fechado segundo essa definição, ele precisa ser lc_at 0, 
ou seja, ele não pode conter nenhum index sem ligações válidas com abstrações. Entendemos melhor essa
propriedade ao analisar a definição recursiva do lc_at. Toda variável livre é localmente fechada. A medida
que um termo será localmente fechado para uma aplicação, se seus dois subtermos também foram localmente fechados.
E para uma abstração, o será se o termo envolvido pela abstração for localmente fechado para k + 1.
Para a variável ligada, portanto, o termo será localmente fechado caso o index i que representa a variável
ligada seja menor do que k. Veja a definição abaixo: *)

Fixpoint lc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_labs t1    => lc_at (S k) t1
  end.

(** O lc_at pode ser usado em diversos teoremas matemáticos relacionados tanto ao open, quanto
à definição de termos. Esses teoremas podem facilitar provas com nível de abstração mais elevado
na teoria do cálculo lambda, permitindo a equivalência entre diferentes tipos e propriedades.*)

(* talvez *)
Lemma lc_at_open_rec_rename: forall t x y m n, lc_at m (open_rec n (pterm_fvar x) t) -> lc_at m (open_rec n (pterm_fvar y) t).
(* begin hide *)
Proof.
  intro t; induction t.
  - intros x y m n0.
    simpl. destruct (n0 === n); subst.
    + intro H.
      auto.
    + intro H; assumption.
  - intros x y m n H.
    auto.
  - intros x y m n. 
    simpl.
    intro H.
    destruct H as [H1 H2].
    split.
    + apply IHt1 with x; assumption.
    + apply IHt2 with x; assumption.
  - intros x y m n.
    simpl.
    intro H.
    apply IHt with x; assumption.
  - intros x y m n.
    simpl.
    intro H.
    apply IHt with x; assumption.
Qed.
(* end hide *)


(* talvez *)
Lemma lc_at_weaken: forall t n m, n <= m -> lc_at n t -> lc_at m t.
(* begin hide *)
Proof.
  intro t; induction t.
  - intros n' m Hleq.
    simpl.
    intro Hlt.
    apply Nat.lt_le_trans with n'; assumption.
  - intros n m Hleq.
    auto.
  - intros n m Hleq.
    simpl.
    intro H.
    destruct H as [H1 H2].
    split.
    + apply IHt1 with n; assumption.
    + apply IHt2 with n; assumption.
  - intros n m Hleq.
    simpl.
    apply IHt.
    apply le_n_S; assumption.
  - intros n m Hleq.
    simpl.
    intro H.
    apply IHt with (S n).
    + apply le_n_S; assumption.
    + assumption.
Qed.
(* end hide *)


(* talvez *)
Lemma lc_at_open: forall t m x, lc_at m ({m ~> pterm_fvar x} t) <-> lc_at (S m) t.
(* begin hide *)
Proof.
  intros t m x; split.
  - generalize dependent x.
    generalize dependent m.
    induction t.
    + intros m x.
      simpl.
      destruct (m === n).
      * subst.
        intro H.
        apply Nat.lt_succ_diag_r.
      * simpl.
        intro H.
        apply Nat.lt_lt_succ_r; assumption.
    + intros m x.
      auto.
    + intros m x.
      simpl.
      intro H.
      destruct H as [H1 H2].
      split.
      * apply IHt1 with x; assumption.
      * apply IHt2 with x; assumption.
    + intros m x.
      simpl.
      apply IHt.
    + intros m x.
      simpl.
      intro H.
      apply IHt with x; assumption.
  - generalize dependent x.
    generalize dependent m.
    induction t.
    + intros m x Hat.
      simpl.
      destruct(m ===n).
      * simpl.
        auto.
      * unfold lc_at in *.
        apply lt_n_Sm_le in Hat.
        apply le_lt_or_eq in Hat.
        destruct Hat.
        ** assumption.
        ** symmetry in H.
          contradiction.
    + intros m x H.
      simpl in *.
      auto.
    + intros m x H.
      simpl in H.
      destruct H as [H1 H2].
      simpl; split.
      * apply IHt1; assumption.
      * apply IHt2; assumption.
    + intros m x H.
      simpl in H.
      simpl.
      apply IHt; assumption.
    + intros m x H.
      simpl in H.
      simpl.
      apply IHt; assumption.
Qed.
(* end hide *)

Lemma term_to_lc_at : forall t, term t -> lc_at 0 t.
(* begin hide *)
Proof.
  intros t Hterm.
  induction Hterm.
  - simpl.
    auto.
  - simpl.
    split; assumption.
  - pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr H1].
    apply H0 in Fr.
    unfold open in Fr.
    apply lc_at_open in Fr.
    assumption.
Qed.
(* end hide *)

(* contra-exemplo: pterm_labs 0
Lemma lc_at_to_term : forall t, lc_at 0 t -> term t.
Proof.
  intro t; induction t using pterm_size_induction.
  - intro H.
    simpl in H.
    inversion H.
  - intro H; apply term_var.
  - simpl.
    intro H.
    destruct H as [H1 H2].
    apply term_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - simpl.
    intro H1.
    apply term_abs with (fv t0).
    intros x Hfv.
    apply H.
    + assumption.
    + reflexivity.
    + unfold open.
      admit.
  - simpl.
    intro H1.
Admitted. *)
  
Lemma lterm_to_lc_at : forall t, lterm t -> lc_at 0 t.
(* begin hide *)
Proof.
  intros t Hterm.
  induction Hterm.
  - simpl.
    auto.
  - simpl; split; assumption.
  - simpl.
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr H1].
    apply H0 in Fr.
    apply lc_at_open in Fr.
    assumption.
  - simpl; split.
    + pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr H2].
    apply notin_union in Fr.
    destruct Fr as [Fr H1].
    apply H0 in Fr.
    apply lc_at_open in Fr.
    assumption.
    + assumption.
Qed.
(* end hide *)

(* Como resolver o problema abaixo?
Theorem : forall v:nat, term (pterm_fvar v) -> lc_at 0 (pterm_fvar v).
Proof.
  intros v H1.
  inversion H1.
Admitted.

Theorem lterm_equiv_lc_at: forall t, lterm t <-> lc_at 0 t.
Proof.
  intro t; split.
  - apply lterm_to_lc_at.
  - intro H. 
    Admitted.

    induction t using pterm_size_induction.
    + intros H1.
      simpl in *.
      inversion H1.
    + intros H1.
      apply lterm_var.
    + simpl. 
      intro H.
      destruct H as [H1 H2].
      apply lterm_app.
      * apply IHt1; assumption.
      * apply IHt2; assumption.
    + simpl. intro Hlc.
      apply lterm_abs with (fv t0).
      intros x Hfv.
      apply H.
      * assumption.
      * reflexivity.
      * apply lc_at_open; assumption.
    + Admitted. *)

(* -Os pré-termos dentro da aplicação e abstrações deveriam ser termos 
   -O lemma provavelmente não pode valer para o caso da variável ligada*)
(*
Lemma Sn_not_body: forall n, not (body (pterm_bvar (S n))).
Proof.
Admitted.

Lemma not_S_is_0: forall n n0, n0 <> S n -> n0 = 0.
Proof.
Admitted.
 *)

(* talvez *)
Fixpoint has_free_index (k:nat) (t:pterm) : Prop :=
  match t with
    | pterm_bvar n => if (k === n) then True else False
    | pterm_fvar x => False
    | pterm_app t1 t2 => (has_free_index k t1) \/ (has_free_index k t2)
    | pterm_abs t1 => has_free_index (S k) t1
    | pterm_labs t1 => has_free_index (S k) t1
  end.

(* begin hide *)
Lemma deMorgan: forall p q, (~ p) /\ (~ q) -> ~(p \/ q).
Proof.
  intros p q H1.
  intros or.
  destruct(or).
  - destruct(H1).
    contradiction.
  - destruct(H1).
    contradiction.
Qed.
(* end hide *)

Lemma term_rename: forall t x y, term (t ^ x) -> term (t ^ y).
(* begin hide *)
Proof.
  intros t x y Hterm.
  apply term_to_lc_at in Hterm.
  Admitted.
(* end hide *)
(*  apply term_equiv_lc_at.
  apply lc_at_open_rec_rename with x.
  assumption.
Qed. *)

(*
  induction t0.
  - intros x y H1.
    unfold open in *.
    destruct(n === 0).
    + rewrite e in *.
      simpl in *.
      apply term_var.
    + admit.
  - intros x y H1.
    unfold open in *.
    simpl in *.
    assumption.
  - intros x y H1.
    unfold open in *.
    simpl in *.
    apply term_app.
    + inversion H1; subst.
      assert(Hyterm := IHt0_1 x y H2).
      assumption.
    + inversion H1; subst.
      assert(Hyterm := IHt0_2 x y H3).
      assumption.
  - intros x y H1.
    unfold open in *.
    admit.
  - admit.
Admitted. *)
Lemma ind_max: forall t u n, term ({n ~> u}t) -> ~ (has_free_index (S n) t).
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma body_not_S: forall t n, body t -> not (has_free_index (S n) t).
(* begin hide *)
Proof.
  intros t0 n H1; induction t0.
  - unfold body in H1.
    unfold has_free_index.
    destruct(S n === n0); subst.
    + destruct H1 as [L].
      pick_fresh x.
      apply notin_union in Fr.
      destruct Fr as [Fr Hn].
      apply H in Fr.
      unfold open in Fr.
      simpl in Fr.
      inversion Fr.
    + intros Htrue.
      assumption.
  - unfold body in H1.
    unfold has_free_index.
    intros HFalse.
    assumption.
  - simpl.
    unfold body in H1.
    destruct H1.
    pick_fresh y.
     apply notin_union in Fr.
     destruct Fr as [Fr H2].
     apply notin_union in Fr.
     destruct Fr as [Fr H1].
     apply notin_union in Fr.
     destruct Fr as [Fr Hn].
     apply H in Fr.
     change (pterm_app t0_1 t0_2 ^ y) with (pterm_app (t0_1 ^ y) (t0_2 ^ y)) in Fr.
     inversion Fr; subst.
     apply deMorgan.
     split.
    + apply IHt0_1.
      unfold body.
      exists (fv t0_1).
      intros x0 Hfv.
      apply term_rename with y.
      assumption.
    + admit.
  - intro Hfree.
    clear IHt0.
    unfold body in H1.
    destruct H1 as [L].
    pick_fresh x.
    apply notin_union in Fr.
    destruct Fr as [Fr H0].
    apply notin_union in Fr.
    destruct Fr as [Fr Hn].
    apply H in Fr.
    unfold open in Fr.
    simpl in Fr.
    inversion Fr; subst.
    pick_fresh z.
    apply notin_union in Fr0.
    destruct Fr0 as [Fr0 Ht0].
    apply notin_union in Fr0.
    destruct Fr0 as [Fr0 Hx].
    apply notin_union in Fr0.
    destruct Fr0 as [Fr0 Hn'].
    apply notin_union in Fr0.
    destruct Fr0 as [Fr0 HL0].
    apply H2 in HL0.
    unfold open in HL0.
    simpl in Hfree.
    clear L H Fr Hn H0 L0 H2 Fr0 Hn' Hx Ht0.
    replace ({0 ~> pterm_fvar z} ({1 ~> pterm_fvar x} t0)) with ({1 ~> pterm_fvar x} ({0 ~> pterm_fvar z} t0)) in HL0.
    + apply ind_max in HL0.
Admitted.
(* end hide *)

Lemma open_rec_close_rec_term: forall t u k, ~(has_free_index k t) -> open_rec k u t = t.
(* begin hide *)
Proof.
  intro t; induction t.
  - intros u k H1.
    simpl.
    destruct(k === n).
    + rewrite <- e.
      admit.
    + reflexivity.
  - intros u k H1.
    simpl.
    reflexivity.
  - intros u k H1.
Admitted.
(* end hide *)

Lemma subst_body: forall t u n, body t -> {S n ~> u} t = t.
(* begin hide *)
Proof.
  intros t u n Hbody.
  apply open_rec_close_rec_term.
  apply body_not_S; assumption.
Qed.  
(* end hide *)
  (*  intros t0 u n Hbody.
  unfold body in Hbody.
  destruct Hbody as [L].
  pick_fresh y.
  apply notin_union in Fr.
  destruct Fr as [Fr H1].
  apply notin_union in Fr.
  destruct Fr as [Fr H2].
  apply notin_union in Fr.
  destruct Fr as [Hbody H3].
  apply H in Hbody.
  clear H3.
  induction Hbody.
  - case(n0 === S n).
    + intros H1.
      subst.
      apply False_ind.
      generalize dependent Hbody.
      apply Sn_not_body.
    + intro HDif.
      apply not_S_is_0 in HDif.
      rewrite HDif.
      reflexivity.
  - simpl.
    reflexivity.
  - unfold body in Hbody.
    destruct Hbody.
    unfold open in H.
    simpl in *.
    rewrite IHt0_1.
    + rewrite IHt0_2.
      * reflexivity.
      * unfold body.
        exists x.
        intros x0 Hnot.
        apply H in Hnot.
        inversion Hnot; subst.
        assumption.
    + unfold body.
        exists x.
        intros x0 Hnot.
        apply H in Hnot.
        inversion Hnot; subst.
        assumption.
  - simpl.
    admit.
  - simpl.
    admit.
Admitted. *)
(*  intros t0 u n Hbody.
  induction t0.
  - case(n0 === S n).
    + intros H1.
      subst.
      apply False_ind.
      generalize dependent Hbody.
      apply Sn_not_body.
    + intro HDif.
      apply not_S_is_0 in HDif.
      rewrite HDif.
      reflexivity.
  - simpl.
    reflexivity.
  - unfold body in Hbody.
    destruct Hbody.
    unfold open in H.
    simpl in *.
    rewrite IHt0_1.
    + rewrite IHt0_2.
      * reflexivity.
      * unfold body.
        exists x.
        intros x0 Hnot.
        apply H in Hnot.
        inversion Hnot; subst.
        assumption.
    + unfold body.
        exists x.
        intros x0 Hnot.
        apply H in Hnot.
        inversion Hnot; subst.
        assumption.
  - simpl.
    admit.
  - simpl.
    admit.
Admitted.
*)
  
Lemma subst_term: forall t u n, term t -> {n ~> u} t = t.
(* begin hide *)
Proof.
  intros t u n H.
  generalize dependent n.
  generalize dependent u.
  induction H.
  - intros u n.
    simpl.
    reflexivity.
  - intros u n.
    simpl.
    rewrite IHterm1.
    rewrite IHterm2.
    reflexivity.
  - intros u n.
    simpl.
    rewrite subst_body.
    + reflexivity.
    + unfold body.
      exists L.
      assumption.
Qed.
(* end hide *)

Lemma subst_lterm: forall t u n, lterm t -> {n ~> u} t = t.
(* begin hide *)
Proof.
  intros t u n H.
  generalize dependent n.
  generalize dependent u.
  induction H.
  - admit.
  - admit.
  - admit.
  - intros u n.
    simpl.
    f_equal.
Admitted.
(* end hide *)    

Lemma abs_body: forall t1 t2 L, (forall x, x \notin L -> t1^x = t2^x) -> pterm_abs t1 = pterm_abs t2.
(* begin hide *)
Proof.
  intro t1; induction t1.
  - intro t2; induction t2.
    + intros L H.
      unfold open in H.
      Admitted.
(* emd hide *)

Lemma subst_open: forall t u x n,  ({S n ~> u} t) ^ x = {S n ~> (u ^ x)} (t ^ x). 
(* begin hide *)
Proof.
  Admitted.
(* end hide *)
  
Lemma subst_term': forall t, (forall u n, term t -> {n ~> u} t = t).
(* begin hide *)
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
Admitted.
(* end hide *)

Lemma subst_lemma_lterms: forall (t1 t2 t3: pterm) (i j:nat), lterm t2 -> lterm t3 -> i <> j -> {j ~> t3} ({i ~> t2} t1) = {i ~> t2} ({j ~> t3} t1).
(* begin hide *)
Proof.
  intro t1; induction t1.
  - intros t2 t3 i j H2 H3 Hle.
    simpl.
    destruct (i ===n); subst.
    + destruct (j === n).
      * symmetry in e.
        contradiction.
      * Admitted.
(* end hide *)

(*    
Lemma subst_lemma_lterms: forall (t1 t2 t3: pterm) (i j:nat), lterm t3 -> i <= j -> {j ~> t3} ({i ~> t2} t1) = {i ~> {j ~> t3} t2} ({S j ~> t3} t1).
Proof.
  intro t1; induction t1.
  - intros t2 t3 i j H3 Hle.
    simpl ({i ~> t2} pterm_bvar n).
    destruct (i === n).
    + subst.
      replace ({S j ~> t3} pterm_bvar n) with (pterm_bvar n).
      * replace ({n ~> {j ~> t3} t2} pterm_bvar n) with ({j ~> t3} t2).
        ** reflexivity.
        ** admit.
      * admit.
    +



Lemma subst_lemma_for_lterms: forall (t1 t2 t3: pterm) (i j:nat), lterm t3 -> i <> j -> {j ~> t3} ({i ~> t2} t1) = {i ~> {j ~> t3} t2} ({j ~> t3} t1).
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
      * rewrite subst_lterm.
        ** reflexivity.
        ** assumption. 
      * simpl.
        destruct (i === n).
        ** contradiction.
        ** reflexivity.
  - intros t2 t3 i h ht3 hdif.
    reflexivity.
  - intros t2 t3 i j ht3 hdif.
    simpl.
    rewrite IHt1_1.
    + rewrite IHt1_2.
      reflexivity.
      * assumption.
      * assumption.
    + assumption.
    + assumption.
  - intros t2 t3 i j ht3 hdif.
    simpl.
    rewrite IHt1.
    + admit.
    + assumption.
    + apply not_eq_S; assumption.
  - intros t2 t3 i j ht3 hdif.
    simpl.
    rewrite IHt1.
    + admit.
    + assumption.
    + apply not_eq_S; assumption.
Admitted.
*)

(*
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

(** * Prova da confluência *)

(** ** O que é confluência *)

(** A confluência no cálculo lambda se define como: Dados dois termos iniciais,
a partir de qualquer conjunto de reduções beta (duas bifurcações quaisquer na árvore de reduções)
 é sempre possível chegar ao mesmo termo resultante (considerando a alfa equivalência). 
Assim, esperamos provar que o cálculo lambda é confluente. Tal característica (confluência) 
permite dizer que o cálculo lambda é determinístico, sendo possível sempre dadas condições iniciais
prever um determinado resultado, ao operar as operações corretas (neste caso, reduções). *)

(** ** Operações necessárias para a prova da confluência *)

(** Já definimos os termos marcados, por meio da criação de uma "marca" em determinados redex's. Um
redex é toda abstração que é base para uma determinada aplicação definida em um determinado termo. Dessa forma, é
necessário definir algumas operações que possam trabalhar com os termos marcados, permitindo que estas marcas
sejam tanto colocadas, quanto retiradas. Geralmente as marcas são criadas na própria definição de uma determinada prova
para então, serem retiradas depois, comparando um termo marcado à um termo não marcado, após uma determinada
sequência de operações do $\lambda$-cálculo, permitindo assim provar determinada hipótese, pois com a marca
é possível acompanhar a o estado de um determinado redex após sucessivas operações. *)

(** Para isso, uma das operações definidas é a operação de apagamento (erase) de marcas, ou melhor,
a operação de apagar. A operação de apagar consiste em, quando da sua aplicação em um termo, apagar
todas as suas (se houverem) marcas, mas preservando a sua estrutura (sem reduzir os redex's). Essa operação
foi definida recursivamente como se segue abaixo, sendo propagada para dentro de cada termo, com atenção
especial à abstração marcada, que transforma-se em abstração, e mantém a propagação do erase. Assim, 
após a aplicação da operação, um termo marcado se tornará um termo sem marcas, e um termo sem marcas não
sofrerá nenhuma alteração.*)

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
(* begin hide *)
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
(* end hide *)
    
Inductive refltrans (red: Rel pterm) : Rel pterm :=
| reflex: forall a, refltrans red a a
| atleast1: forall a b, red a b -> refltrans red a b
| rtrans: forall a b c, refltrans red a b -> refltrans red b c -> refltrans red a c.

Inductive refltrans' (red: Rel pterm) : Rel pterm :=
| refl: forall a, refltrans' red a a
| rtrans': forall a b c, red a b -> refltrans' red b c -> refltrans' red a c.

Lemma refltrans_equiv: forall (R: Rel pterm) (a b: pterm), refltrans R a b <-> refltrans' R a b.
(* begin hide *)
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
(* end hide *)

(** A beta redução do cálculo lambda é a reduçao de um redex... Explicar as definições mais abaixo...*)

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

(** Dessa forma, também é necessária a definição da função phi. A função phi também trabalha
com marcas, assim como o erase, no entanto possui um funcionamento um pouco distinto. A função phi
possui o papel de, ao ser aplicada em um termo, reduzir todos os redex's marcados (abstrações
com marcas com um determinado termo sendo aplicado). Dessa forma, após a aplicação da operação phi
um termo marcado torna-se um termo sem marcas, porém difere estruturalmente do seu estado anterior,
pelo fato de agora possuir os antigos redexs marcados reduzidos. Perceba que um termo sem marcas, ao
receber a aplicação de phi permanece inalterado, por definição. Definimos a operação como se segue logo
abaixo, recursivamente, a operação phi é propaga pelo termo que sofre a aplicação, reduzindo os redex's
marcados, o encontrar uma aplicação onde o termo mais à esquerda é uma abstração marcada.*)

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
(* begin hide *)
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
        Admitted.
(* end hide *)

Corollary phi_open: forall t x, phi(t^x) = (phi t)^x.
(* begin hide *)
Proof.
  intros t x.
  unfold open.
  Admitted.
(* end hide *)
  (* apply phi_open_rec.
Qed.
   *)
  
Lemma phi_term: forall t, lterm t -> term (phi t).
(* begin hide *)
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
Admitted.
(* end hide *)

Lemma term_fvar_to_term: forall t1 t2 t3 x, term (phi (pterm_app t1 t2)^x) -> term t3 -> term (phi (pterm_app t1 t2)^^t3). 
(* begin hide *)
Proof.
Admitted.  
(* end hide *)

Lemma term_phi_open: forall t1 t2 x L,  x \notin L -> term (phi (t1 ^ x)) -> term (phi t2) -> term (phi t1 ^^ phi t2).
(* begin hide *)
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
   (* rewrite phi_open_rec in Hterm1.
    apply term_fvar_to_term with x; assumption.
  - intros t2 x L HL Hterm1 Hterm2.
    assert(teste := IHt t2 x L HL).
    admit.  Gabriel *)
Admitted.
(* end hide *)
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
(* begin hide *)
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
(* end hide *)

Lemma lterm_preserves_bvar : forall M n, erase M = (pterm_bvar n) -> M = (pterm_bvar n).
(* begin hide *)
Proof.
  Admitted.
(* end hide *)

Lemma lterm_preserves_app : forall M N L, erase M = (pterm_app N L) -> exists N' L', M = (pterm_app N' L').
(* begin hide *)
Proof.
(*
  exists (erase N).
  exists (erase L). *)
  Admitted.
(* end hide *)

Lemma lterm_preserves_abs : forall M N, erase M = (pterm_abs N) -> exists N', M = (pterm_abs N') \/ M = (pterm_labs N').
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma open_rec_preserves_labs: forall t u k, (open_rec k u (pterm_labs t)) = (pterm_labs (open_rec (S k) u t)).
(* begin hide *)
Proof.
  intros t u k .
  reflexivity.
Qed.
(* end hide *)
  
Lemma erase_open_rec : forall (M N: pterm) (k : nat), erase ({k ~> N} M) = {k ~> (erase N)} (erase M).
(* begin hide *)
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
(* end hide *)

Corollary erase_open : forall M N: pterm, erase (M ^^ N) = (erase M) ^^ (erase N).
(* begin hide *)
Proof.
  unfold open.
  intros M N.
  apply  erase_open_rec.
Qed.
(* end hide *)

Lemma phi_subst_rec: forall (M N: pterm) (k: nat), term N -> phi ({k ~> N} M) = {k ~> (phi N)}(phi M).
(* begin hide *)
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
(* end hide *)

Corollary phi_subst: forall M N, phi (M ^^ N) = (phi M) ^^ (phi N). 
(* begin hide *)
Proof.
  Admitted.
(* end hide *)

Lemma phi_prop: forall M N : pterm, lterm M -> lterm N -> (M -->>lB N) -> (phi M) -->>B (phi N).
(* begin hide *)
Proof.
  intros M N Hterm1 Hterm2 H.
  induction H.
  - Admitted.
(* end hide *)

  
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
(* begin hide *)
Proof.
Admitted.
(* end hide *)

Lemma erase_prop1 : forall M N: pterm, term M -> term N -> (M -->B N) -> forall M' N', (erase M' = M) /\ (erase N' = N) ->  (M' -->lB N').
(* begin hide *)
Proof.
  intros M N HtM HtN Hred.
  
  induction Hred.
  - inversion H; subst.
   (* apply erase_prop_str in H2.
    destruct H2 as [u0].
    destruct H2 as [v].*)
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
(* end hide *)

Lemma erase_prop : forall M N M' N': pterm, term M -> term N -> (M -->>B N) -> erase M' = M -> erase N' = N ->  (M' -->>lB N').
(* begin hide *)
Proof.
  intros M N M' N' HtM HtN Hred HeM HeN.
  induction Hred.
  - Admitted.
(*    apply reflex.
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
    + Admitted *)

(*
Lemma erase_lbeta_2313: forall t1 t2, t1 -->>B t2 -> (forall t1', erase(t1') = t1 -> forall t2', erase(t2') = t2 -> t1' -->>lB t2').
Proof.
Admitted.
*)
(* end hide *)

Lemma phi_preserves_term: forall t, term t -> term (phi t).
(* begin hide *)
Proof.
  intros t H.
  induction H.
  Admitted.
(* end hide *)
  
Lemma beta_phi_one_step: forall t1 t2, t1 -->lB t2 -> phi(t1) -->B phi(t2).
(* begin hide *)
Proof.
  intros t1 t2 H.
  induction H.
  - inversion H; subst.
    + simpl.
      rewrite phi_subst.
      apply redex.
      apply reg_rule_b.
      * admit.        
      * apply phi_preserves_term; assumption.
    + Admitted.
(* end hide *)  

Lemma beta_phi: forall t1 t2, t1 -->>lB t2 -> phi(t1) -->>B phi(t2).
(* begin hide *)
Proof.
  intros t1 t2 H.
  induction H.
  - apply reflex.
  - apply beta_phi_one_step in H.
    apply atleast1; assumption.
  - Admitted.
(* end hide *)

Lemma erase_phi: forall t t1 t2, erase(t) = t1 -> phi(t) = t2 -> t1 -->>B t2.
(* begin hide *)
Proof.
  (*intros t0 t1 t2 Herase Hphi.
  induction t0.
  - simpl in *.
    rewrite Herase in Hphi.
    rewrite Hphi.
    apply reflex.
  - simpl in *.
    rewrite Herase in Hphi.
    rewrite Hphi.
    apply reflex.
  - (*seems that we have a contradiction, this just will occur if t0_1 do not 
      have a lterm*)
    simpl in Herase. *)

  intro t; induction t using pterm_size_induction.
  - intros t1 t2 Herase Hphi.
    simpl in *.
    rewrite Herase in Hphi.
    rewrite Hphi.
    apply reflex.
  - intros t1 t2 Herase Hphi.
    simpl in *.
    rewrite Herase in Hphi.
    rewrite Hphi.
    apply reflex.
  - 
  Admitted.
(* end hide *)

Lemma term_erase: forall t, term t -> erase(t) = t.
(* begin hide *)
Proof.
  Admitted.
(* end hide *)

Lemma body_erase: forall t, body t -> erase(t) = t.
(* begin hide *)
Proof.
  Admitted.
(* end hide *)

(* begin hide *)
  (* esconde código *)

(** * Seção *)

(** ** Subseção *)

(** texto do relatório *)

(* end hide *)

(* end hide *)
          


(** * O strip_lemma *)

(** O strip_lemma é muito importante para a prova da confluência do cálculo lambda, utilizando
a abordagem de Barendregt (citar). O strip_lemma prova a propriedade de que: Se um termo reduz em um
passo para t1, e também reduz em n passos para t2, então existe um t3 tal que t1 reduz em n passos para t3
e t2 reduz em n passos para t3. *)

(** Perceba que essa propriedade ainda não prova a nossa definição de confluência, mas está um passo
atrá de tal prova. Ao provar o strip_lemma e algumas outras propriedades, a prova da confluência do cálculo
lamba é direta. De outra forma, podemos dizer que a prova da confluência no cálculo lambda é uma 
generalização do strip_lemma. Aida não conseguimos fechar a prova formal do strip_lemma, mas iremos
apresentar logo abaixo os nossos avanços e apresentar quais os próximo passos que devemos seguir.*)

(** ** formalização da prova do strip_lemma *)

(** Para realizar a prova do strip_lemma iremos considerar os termos t, t1 e t2. Porém, para isso, iremos
considerar que o termo t possui em sua composição o seguinte redex: pterm_app (pterm_labs Q) P, e apenas
iremos levar em conta este redex marcado para construir as nossas operações. Ou seja, o termo deverá conter apenas
um redex marcado, para podermos acompanhar o seu estado ao longo das operações de prova que serão realizadas.
Dessa forma devemos considerar o seguinte: t1 é o termo obtido ao aplicar uma beta redução marcada em t, 
e reduzir especificamente o redex marcado apresentado. Nesse caso, portanto, aplicando phi(t) temos t1. Ou seja:*)

(** $ phi(t) = t1 $ *)

(** Com isso, podemos dizer que existe um termo t' cuja erase(t) = t', e t' ->B t1. Assim
podemos reduzir t' para t2 via n reduções beta, e provar que t1 tabém reduz para t2 via n beta reduções. O que está sendo 
realizado neste caso é a manutenção de um redex marcado, após n beta reduções quaisquer, que não ocorrem no redex marcado. 
Em seguida o erase e a função phi são utilizados para demonstrar que os termos convergem em t2. Como esses termos são quaisquer
e a única característica com a qual estamos trabalhando é a marca, então a prova pode ser generalizada para qualquer caso.*)

(** Exemplificando um pouco melhor, uma espécie de contador, como o abaixo poderia ser utilizado para se certificar de que
o termo que está sendo trabalhado é um termo com apenas um redex marcado. Este é um dos caminhos de prova com o qual estamos
trabalhando no projeto.*)

Fixpoint lredex_count (t:pterm):(nat) :=
match t with
  | pterm_bvar i => 0
  | pterm_fvar x => 0
  | pterm_app t1 t2 => (lredex_count t1) + (lredex_count t2)
  | pterm_abs t1    => (lredex_count t1)
  | pterm_labs t1   => 1 + (lredex_count t1)
end.

(* Como definir essa operação???? 
Fixpoint oneredex (t:pterm): Set :=
  | one_redex_pterm : forall (x : pterm), lredex_count x = 1 -> Prop.
*)

(* não estou conseguindo executar o theorem abaixo *) 


  (** A prova será realizada por meio da indução na estrutura da beta redução de t para t1. Assim chegamos a quatro
casos. Estes casos são relativos à própria estrutura da beta redução de t para t1. Ao provar os passos anteriores, 
a prova se completa por indução para o caso geral. No entanto, a definição atual do strip_lemma
está muito generalizada, não havendo, por exemplo, um termo marcado definido com apenas uma marca que possa ser acompanhada
durante a prova. Nesse caso, vamos utilizar a notação de nomes locais sem marcas e o trabalho de \cite{chatgerout} (citar certo)
para nos ajudar a completar a prova mesmo de maneira generalizada, mas também apresentamos opções ilustrativas mais abaixo.   *)

  (** Dado esse contexto, dois caminhos podem ser seguidos: No primeiro, a definição do teorema poderia ser refeita, de uma
maneira menos generalizada, abarcando as marcas e utilizando alguma ideia semelhante à apresentada na função lredex_count. O segundo 
caminho, seria a construção de diversos lemas auxiliares que permitiriam com que o teorema geral pudesse ser provado. Na realidade
o sucesso em realizar esta prova provavelmente depende um caminho intermediário entre essas duas opções. Atualmente, seguimos o
caminho da criação de diversos lemas auxiliares, como vamos explanar mais abaixo. Mas, em vistas de ilustrar uma opção de prova 
diferente, apresentamos abaixo uma definição menos genralizada para o teorema como exemplo: *)

  (** $ Theorem strip_lemma: forall  lterm_one t', term t t1 t2, erase(t') = t -> phi(t') = t1 ->
t -->B t1 -> t -->>B t2 -> exists t3, t1 -->>B t3 /\ t2 -->>B t3. $ *)

  (** Onde lterm_one é a definição de um termo marcado qualquer, que possui apenas uma marca. t' é um termo com as mesmas propriedades
estruturais de t, exceto pelo redex marcado, sendo isto definido pela igualdade $ erase(t') = t $ e t1 é o termo cuja estrutura
reduz de t com uma beta redução no redex marcado, o que é nesse caso definido pela igualdade $ phi(t') = t1 $. Assim, como t é um
termo qualquer com ao menos um redex, a prova é suficiente para o strip_lemma. Lembramos que essa pode não ser a melhor abordagem para
um assistente de provas, mas exemplifica muito bem o que \cite{barendregt} (melhorar citação) fez em sua prova, podendo ser tomado como base para o sucesso
na formalização dessa prova. *)

(** *** Prova formal do strip_lemma, com a definição generalizada *)

Theorem strip_lemma: forall  t t1 t2, t -->B t1 -> t -->>B t2 -> exists t3, t1 -->>B t3 /\ t2 -->>B t3.
Proof.
  intros t t1 t2 H1 H2.

  (** Iniciamos com a indução na estrutura da beta redução em um passo (de t para t1 na notação utilizada):*)

  induction H1.

  (** A prova se divide em 4 ramos, e podemos perceber que nenhum deles é um caso simples. Os detalhes das operações de prova mais
abaixo são irrelevantes para os objetivos deste relatório, e por isso não serão apresentados. Incentivamos que as operações sejam
copiadas, caso haja o interesse em continuar a prova deste ponto de partida.*)

  - inversion H; subst.
    apply refltrans_equiv in H2.
    remember (t1 ^^ u) as b.
    generalize  dependent b.
    induction H2.
    + exists (t1 ^^ u); split.
(*A prova parou aqui*)
      * apply reflex.
      * apply atleast1.
        apply redex.
        assumption.
    + inversion H; subst.
      rewrite <- H3 in H.
      clear H0 H1 H3.

      inversion H2; subst.
      * admit.
      * admit.
      * admit.
    + 
      apply open_rec_inj in H3.
      destruct H3 as [Heq1 Heq2]; subst.
      clear H4 H6.
      induction H2.
      * Admitted.
      

      
    (** A definição do lemma erase_lbeta_2313 trabalha com a equivalência, dados termos de mesma estrutura porém dois com
marcas e dois sem marcas, da redução destes pares de termos pelas beta reduções marcadas e não marcadas. Essa definição é
necessária para trabalhar com a marca e a acompanhar de modo a ser possível enxergar os estados da estrutura com a qual estamos
trabalhando. *)


    Lemma erase_lbeta_2313: forall t1 t2, t1 -->>B t2 -> forall t1' t2', erase(t1') = t1 /\ erase(t2') = t2 -> t1' -->>lB t2'.
    Proof.
      Admitted.

    assert (H': pterm_app (pterm_labs t1) u -->>B t2).
    {
      apply erase_lbeta_2313.
    }
     in H2 with (pterm_app (pterm_labs t1) u) _.
    

  
  assert (H2' := H2).
  assert (forall t', erase(t') = t -> forall t2', erase(t2') = t2 -> t' -->>lB t2').
  {
    apply erase_lbeta; assumption.   
  }
  inversion H1; subst.
  - inversion H0; subst.
    assert (erase (pterm_app (pterm_labs t0) u) = pterm_app (pterm_abs t0) u -> forall t2', erase t2' = t2 -> pterm_app (pterm_labs t0) u -->>lB t2').
    {
      apply H.
    }
    clear H.
    assert (erase (pterm_app (pterm_labs t0) u) = pterm_app (pterm_abs t0) u).
    {
      simpl.
      rewrite body_erase.
      - rewrite term_erase.
        + reflexivity.
        + assumption.
      - assumption.
    }
    assert (forall t2' : pterm, erase t2' = t2 -> pterm_app (pterm_labs t0) u -->>lB t2').
    {
      apply H5.
      assumption.
    }
    clear H H5.
    Admitted.



