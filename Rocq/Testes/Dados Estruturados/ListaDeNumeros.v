Inductive listanatural : Type :=
   | nil (* lista vazia *)
   | cons (n : nat) (l : listanatural). (* lista construída com outros dois tipos de dados - um número natural e outra lista *)

Definition minhalista := cons 1 (cons 3 nil).

(* Nova notação *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Agora todas essas definições significam a mesma coisa *)
Definition minhalist1 := 1 :: (2 :: (3 :: nil)).
Definition minhalist2 := 1 :: 2 :: 3 :: [].
Definition minhalist3 := [1;2;3].

(* Funções em Listas *)

Fixpoint repete (n count : nat): listanatural :=
   match count with
   | 0 => nil
   | S count' => n :: (repete n count')
   end.

Compute repete 42 3. (* [42; 42; 42]*)


Fixpoint tamanho (lst : listanatural) : nat :=
   match lst with
   | nil => 0
   | h :: t => S (tamanho t)  (* h : head (cabeça), t: tail (calda) *)
   end.

Compute tamanho (repete 42 3). (* = 3 : nat *)


Fixpoint juntar (l1 l2 : listanatural) : listanatural :=
   match l1 with
   | [] => l2
   | h :: t => h :: (juntar t l2)
   end.

Compute juntar [1;2;3][4;5;6]. (* [1; 2; 3; 4; 5; 6]*)

(* Mudando notação de juntar *)
Notation "x ++ y" := (juntar x y)(right associativity, at level 60).

Example teste_juntar1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example teste_juntar2: [] ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example teste_juntar3: [1;2;3] ++ [] = [1;2;3].
Proof. reflexivity. Qed.

(* Funções Head e Tail *)
Definition hd (default: nat) (l : listanatural) : nat :=
   match l with
   | [] => default (* Lista vazia não tem head, ao invés de levantar exceção ele passa um valor default *)
   | h :: t => h
   end.

Definition tl (l : listanatural) : listanatural :=
   match l with 
   | [] => []
   | h :: t => t
   end.


Example teste_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example teste_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example teste_hd3: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* Teorema com Listas *)
Theorem nil_juntar : forall (lst : listanatural),
   [] ++ lst = lst.
Proof. reflexivity. Qed.

Theorem tl_tamanho_predecessor: forall (lst:listanatural),
   pred (tamanho lst) = tamanho (tl lst). (* tamanho da lista - 1 = tamanho do tail *)

Proof.
    intros lst. destruct lst as [| h t].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.