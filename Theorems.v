Inductive Exp := 
  | Var : Exp
  | Lit : nat -> Exp
  | Add : Exp -> Exp -> Exp
  | If0 : Exp -> Exp -> Exp -> Exp.

Fixpoint eval (e : Exp) (n : nat) : nat :=
  match e with
      | Var => n
      | Lit i => i
      | Add e1 e2 => eval e1 n + eval e2 n
      | If0 e1 e2 e3 => 
         match eval e1 n with
           | 0 => eval e2 n
           | _ => eval e3 n
         end
  end.

Inductive SValue := 
  | SVar : SValue 
  | SLit : nat -> SValue
  | SAdd : SValue -> SValue -> SValue.

Inductive ETree := 
  | Val  : SValue -> ETree
  | Fork : SValue -> ETree -> ETree -> ETree.

Fixpoint mergeST (s1 : SValue) (t : ETree) : ETree :=
  match t with
      | Val s2 => Val (SAdd s1 s2)
      | Fork s2 t1 t2 => Fork s2 (mergeST s1 t1) (mergeST s1 t2)
  end.

Fixpoint mergeTT (t1 : ETree) (t2 : ETree) : ETree :=
  match t1 with
      | Val s1 => mergeST s1 t2
      | Fork s t3 t4 => Fork s (mergeTT t3 t2) (mergeTT t4 t2)
  end.

Fixpoint propagate (t1 : ETree) (t2 : ETree) (t3 : ETree) : ETree :=
  match t1 with
      | Val s => Fork s t2 t3
      | Fork s t4 t5 => Fork s (propagate t4 t2 t3) (propagate t5 t2 t3)
  end.

Fixpoint seval (e : Exp) : ETree :=
  match e with
      | Var => Val SVar
      | Lit i => Val (SLit i)
      | Add e1 e2 => mergeTT (seval e1) (seval e2)  
      | If0 e1 e2 e3 => propagate (seval e1) (seval e2) (seval e3)
  end.

Inductive Path :=
  | Leaf : SValue -> Path
  | TCondition : SValue -> Path -> Path
  | FCondition : SValue -> Path -> Path.

Require Import Coq.Lists.List.

Fixpoint paths (e : ETree) : list Path :=
  match e with
      | Val s => cons (Leaf s) nil
      | Fork s t1 t2 => 
        (map (fun p => TCondition s p) (paths t1)) ++ (map (fun p => FCondition s p) (paths t2))
  end.

Definition epaths (e : Exp) : list Path := paths (seval e).

Fixpoint exec (s : SValue) : nat -> nat :=
  match s with
      | SVar => fun x => x
      | SLit i => fun x => i
      | SAdd s1 s2 => fun x => (exec s1 x) + (exec s2 x)
  end.

Fixpoint path2theorem (p : Path) (ef : nat -> nat) (x : nat) : Prop :=
  match p with
      | Leaf s => ef x = exec s x
      | TCondition s p1 => (exec s x = 0) -> path2theorem p1 ef x
      | FCondition s p1 => (not (exec s x = 0)) -> path2theorem p1 ef x
  end.

Fixpoint paths2theorem (ps : list Path) (ef : nat -> nat) (x : nat) : Prop :=
  match ps with
      | nil => True
      | cons y ys => path2theorem y ef x /\ paths2theorem ys ef x
  end.

Definition ptheorem (e : Exp) : Prop :=
  forall x, paths2theorem (epaths e) (eval e) x.

Definition program := If0 Var (Lit 0) (Lit 1).

Definition program2 := If0 program Var (Lit 3).

Eval compute in ptheorem program.
Eval compute in ptheorem program2.

Lemma t : ptheorem program.
unfold ptheorem.
intros.
simpl.
split.
intros.
rewrite H.
reflexivity.
split.
intros.
assert (exists y, x = S y).
admit.
destruct H0.
rewrite H0.
reflexivity.
auto.
Qed.

Lemma soundness : forall (e : Exp), ptheorem e.
intros.
induction e; unfold ptheorem; simpl; intros.
(* Case Var *)
split.
reflexivity.
auto.
(* Case Lit *)
split.
reflexivity.
auto.
(* Case (Add e1 e2) *)
unfold epaths.
simpl.
unfold ptheorem in IHe1.
Admitted.

Lemma sound_path : forall (e : Exp) (p : Path), 
                     In p (epaths e) -> forall x, path2theorem p (eval e) x.
Proof. 
induction e; simpl; intros.
(* case Var *)
destruct H.
rewrite <- H.
simpl.
reflexivity.
destruct H.
(* Case Lit *)
destruct H.
rewrite <- H.
simpl.
reflexivity.
destruct H.
unfold epaths in H.
simpl in H.


