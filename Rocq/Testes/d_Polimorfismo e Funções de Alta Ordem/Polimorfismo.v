(* Listas polifórmicas *)
(* Ao invés de criarmos uma lista para cada tipo, podemos
 usar uma definição polifórmica que permite implementar 
 listas de qualquer tipo *)

 Inductive lista (X : Type) : Type := (* Parecido com Generics em Java *)
 | nil 
 | cons (x : X)(l : lista X). (* x seria head do tipo X passado e l seria tail do tipo X passado *)

 (* list é uma função de types para types *)
 Check lista : Type -> Type.

 (* O 'X' na definição de 'lista' se torna um parâmetro  para os construtores da lista 'nil' e 'cons' *)
 Check (nil nat) : lista nat.

 Check (cons nat 3 (nil nat)) : lista nat.

 Check nil : forall (X : Type), lista X.

 Check cons : forall (X : Type), X -> lista X -> lista X.

 Check (cons nat 2 (cons nat 1 (nil nat))) : lista nat.

 (* Versões polimórficas de funções apresentadas anteriormente *)

 Fixpoint repete (X : Type)(x : X)(count : nat) : lista X :=
    match count with
    | 0 => nil X 
    | S count' => cons X x (repete X x count')
    end.

Example teste_repete1 :
   repete nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Proof.
reflexivity. Qed.

Example teste_repete2 :
   repete bool false 1 = cons bool false (nil bool).

Proof.
reflexivity. Qed.