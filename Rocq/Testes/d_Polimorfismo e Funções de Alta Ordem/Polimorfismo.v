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

(* Simplificando a notação *)
(* Podemos usar a inferência de tipos do Rocq *)

Fixpoint repete' X x count : lista X :=
   match count with
   | 0 => nil X
   | S count' => cons X x (repete' X x count')
   end.

Check repete' 
   : forall X : Type, X -> nat -> lista X.
Check repete
   : forall X : Type, X -> nat -> lista X.

(* Podemos substituir o X pelo coringa '_' nas definições *)
Fixpoint repete'' X x count : lista X :=
   match count with
   | 0 => nil _
   | S count' => cons _ x (repete'' _ x count')
   end.

Definition lista123' :=
   cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Ao invés de escrevermos esses símbolos repetidamente, 
podemos dizer ao Rocq para inferir isso, através do comando
Argument. Argument diz para sempre tratar um argumento c
omo implícito *)

Arguments nil {X}. (* nil - nome da função ou construtor ou qualque valor que estamos tratando. X - o argumento que vai ser tratado implicitamente *)
Arguments cons {X}.
Arguments repete {X}.

Definition lista123'' := cons 1 (cons 2 (cons 3 nil)).

(* Podemos fazer isso já na definição da função.
Ao invés de usarmos Arguments, usamos '{}' na declaração 
da função *)

Fixpoint repete''' {X : Type}(x : X)(count : nat) : lista X :=
   match count with
   | 0 => nil
   | S count' => cons x (repete''' x count')
   end.

(* Versões polimórficas de funções vistas anteriormente *)

Fixpoint juntar {X : Type}(l1 l2 : lista X) : lista X :=
   match l1 with
   | nil => l2
   | cons h t => cons h (juntar t l2)
   end.

Fixpoint reverter {X : Type}(l : lista X) : lista X :=
   match l with
   | nil => nil
   | cons h t => juntar (reverter t) (cons h nil)
   end.

Fixpoint tamanho {X : Type}(l : lista X) : nat :=
   match l with
   | nil => 0
   | cons _ l' => S(tamanho l')
   end.

Example teste_rev1 :
   reverter (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof.
reflexivity. Qed.

Example teste_rev2 :
   reverter (cons true nil) = cons true nil.
Proof.
reflexivity. Qed.

Example teste_tamanho1 :
   tamanho (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof.
reflexivity. Qed.

(* Provendo Tyoe Arguments explicitamente *)

Fail Definition meu_nil := nil. (* Rocq não vai saber inferir o tipo de nil *)

(* Podemos dar um argumento explicitamente *)
Definition meu_nil : lista nat := nil.

(* Ou podemos usar '@' para tornar explícitos argumentos que eram implícitos*)
Check @nil : forall X : Type, lista X.

Definition meu_nil' := @nil nat.

(* Tornando as notações padrões *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y [])..).

Notation "x ++ y" := (juntar x y)
                     (at level 60, right associativity).
                  
Definition lista123''' := [1;2;3].

(* Provando teoremas com as novas notações *)

Theorem juntar_assoc : forall X (lst1 lst2 lst3 : lista X),
   lst1 ++ lst2 ++ lst3 = (lst1 ++ lst2) ++ lst3.

Proof.
   intros X lst1 lst2 lst3. induction lst1 as [| h1 t1].
   - simpl. reflexivity.
   - simpl. rewrite IHt1. reflexivity.
Qed.

