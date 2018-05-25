(*Require Import PeanoNat.*)
Require Import List.
Require Import NAxioms NProperties OrdersFacts.

Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x , y , .. , z ] " := (cons x (cons y .. (cons z nil) ..)).
Notation " ( x :: l ) " := (cons x l).


(*Using de Bruijn indexes*)
Inductive MLexp : Set :=
  | Var : nat -> MLexp
  | Appl : MLexp -> MLexp -> MLexp
  | Lambda : MLexp -> MLexp
  | Let : nat -> MLexp -> MLexp -> MLexp.


(*We can now see the price we are paying for de Bruijn notatio; readability*)
 
(*λx.x*)
Compute Lambda (Var 0).

(*let x = λx.x in xx*)
Compute Let 0 (Lambda (Var 0)) (Appl (Var 0) (Var 0)).

Inductive type: Set :=
  | TVar: nat -> type
  | Arrow: type -> type -> type. (*ej. t1->(t2->t2)*)

(*Lenguajes con anotaciones de tipos*)
Inductive MLexpT : Set :=
  | VarT : nat -> MLexpT
  | ApplT : MLexpT -> MLexpT -> MLexpT
  | LambdaT : MLexpT -> type -> MLexpT
  | LetT : nat -> MLexpT -> type -> MLexpT -> MLexpT.


Fixpoint eq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

Fixpoint elem (n:nat) (l:list nat):bool:=
  match l with
  |[] => false
  |(x::xs) => if eq_nat n x then true else elem n xs
  end.

Fixpoint leb (x y: nat): bool :=
match x,y with
  | 0, _ => true
  | _, 0 => false
  | S n', S m' => leb n' m'
end.

Fixpoint max_aux (n:nat) (l:list nat):nat := 
  match l with 
  |[] => n
  |(x::xs) => if  (leb x n) then (max_aux n xs) else (max_aux x xs)
  end.

Fixpoint max (l:list nat):nat := max_aux 0 l. 


Inductive option (A : Set) : Set :=  | None : (option A) 
  | Some : A -> (option A).

Definition substitution := list (nat*type).


Fixpoint apply_subs t:= fix apply_subs1 (s:substitution):= 
  match t with
  |TVar n => match s with
             |[] => TVar n
             |((m,t1)::xs) => if eq_nat n m then t1 else apply_subs1 xs
             end
  |Arrow t1 t2 => Arrow (apply_subs t1 s) (apply_subs t2 s)
  end.



Definition ctx := list type.

Definition newVT (l:list nat):type := TVar (S(max l)).

(*A judgement is a triplet of ctx, the converted expression to type annoted expr and the type of the expression.*)

Inductive has_type: Type :=
| ht: ctx -> MLexpT -> type -> has_type.
 
Fixpoint vtype_list (t:type):list nat :=
  match t with 
  |TVar n => [n]
  |Arrow t1 t2 => app (vtype_list t1) (vtype_list t2)
  end.

Fixpoint simpSust (s:substitution):substitution :=
  match s with 
  |[]=>[]
  |((n,t)::xs) => match t with
                 |TVar m => if eq_nat n m then simpSust xs else ((n,t)::(simpSust xs))
                 |t1 => ((n,t1)::(simpSust xs))
                 end
  end.

Fixpoint map_subst (s : substitution) (pair: (nat*type)):substitution :=
match s with 
  |[] => []
  |((n,t)::xs) => (n, apply_subs t [pair])::(map_subst xs pair)
end.

Fixpoint compSustAux (s1 s2:substitution):substitution :=
match s2 with
  |[] => []
  |(x::xs) => compSustAux (map_subst s1 x) xs
end.

Definition compSust (s1 s2:substitution):substitution := (compSustAux s1 s2) ++ s2.

Fixpoint unify (t1 t2:type):substitution :=
  match t1, t2 with
  |TVar n,TVar m => if eq_nat n m then [] else [(n,TVar m)]
  |TVar n, vt => if elem n (vtype_list vt) then [] else [(n,vt)]
  | Arrow r1 r2, Arrow s1 s2 => let sust1 := unify r1 s1 in let sust2 := unify r2 s2 in compSust sust1 sust2
  |_, _ => []
  end.


Fixpoint erase (e : MLexpT) : MLexp :=
match e with
  | VarT n => Var n
  | ApplT e1 e2 => Appl (erase e1) (erase e2)
  | LambdaT e' _ => Lambda (erase e')
  | LetT n e1 _ e2 => Let n (erase e1) (erase e2)
end.

Fixpoint eqb n m: bool :=
match n, m with
  | 0, 0 => true 
  | 0, _ => false
  | _, 0 => false
  | S n', S m' => eqb n' m'
end.

Fixpoint eqType (t1 t2: type): bool :=
match t1,t2 with
  | TVar n, TVar m => eqb n m
  | Arrow r1 r2, Arrow s1 s2 => andb (eqType r1 s1) (eqType r2 s2)
  | r, s => false
end.

Fixpoint getCommonTypes (c1 c2 :ctx) : ctx:=
match c1, c2 with
  | [], _ => []
  | _, [] => []
  | t1::xs, t2::ys => if (eqType t1 t2) then t1::(getCommonTypes xs ys) else getCommonTypes xs ys
end.

Fixpoint applySustCtx (c :ctx) (l : list substitution) : ctx := [].

(*Fixpoint w (e : MLexp) (y : list type) : (has_type*list type) :=
match e with
  | Var x => let z := newVT y in (([z], (VarT x),z), y ++ [z])
  | Appl e1 e2 => let new_type := newVT y in (let ((ctx1, e1',t1), types) := (w e1) in 
                                              let ((ctx2, e2',t2), types2) := (w e2) in
                                               let umg := ((getCommonTypes ctx1 ctx2) ++ [(Arrow t1 new_type), (Arrow t2 new_type)])in 
                                               (((applySystCtx (ctx1 ++ ctx2) umg), AppT e1' e2', new_type),(vrs1 ++ vrs2 ++ [new_type])))
  |
  |
end.*)

Variable err:ctx.
Variable err2:MLexpT.
Variable err3:type.

Fixpoint type_nat (l: list type) : list nat :=
match l with 
  | [] => []
  | (TVar n):: xs => n :: (type_nat xs)
  | x::xs => type_nat xs
end.

Fixpoint algoritmoW (e : MLexp) (y : list type) : has_type := 
match e with
  | Var n => let z := newVT (type_nat y) in ht [z] (VarT n) z
  | Appl e1 e2 => let new_type := newVT (type_nat y) in match algoritmoW  e1 [new_type], algoritmoW e2 [new_type] with
                   | ht ctx1 e1' t1, ht ctx2 e2' t2 => ht (ctx1 ++ ctx2 ++ [(Arrow t1 new_type), (Arrow t2 new_type)]) (ApplT e1' e2') new_type
                  end
  | Lambda e' => let new_type := newVT (type_nat y) in match algoritmoW e' [new_type] with
                   | ht ctx1 e1 t1 => ht (ctx1 ++ [(Arrow t1 new_type)]) (LambdaT e1 t1) new_type
                  end 
  | Let n e1 e2 => match algoritmoW e1 [], algoritmoW e2 []with
                   | ht ctx1 e1' t1, ht ctx2 e2' t2 => ht (ctx1 ++ ctx2) (LetT n e1' t1 e2') t2
                  end
end.

Theorem erase_e:  forall (e: MLexp) (c: ctx) (t : type) (e' : MLexpT), algoritmoW e [] = ht c e' t -> erase e' = e.
Proof.
  intros.
  induction e.
  inversion H.
  unfold erase.
  trivial.
  inversion H.
Admitted.

Theorem exitens: forall (e: MLexp), exists (c: ctx) (t : type) (e' : MLexpT), algoritmoW e [] = ht c e' t.
Proof.
  intros.
  induction e.
  unfold algoritmoW.
  exists (newVT (type_nat []) :: []).
  exists (newVT (type_nat [])).
  exists (VarT n).
  trivial.
  