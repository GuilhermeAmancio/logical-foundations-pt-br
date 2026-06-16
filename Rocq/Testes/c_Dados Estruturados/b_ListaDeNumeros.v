Require Import Arith.
Require Import Nat.

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

Example teste_tl: tl [1;2;3] = [2;3].
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

(* Usando induções em teoremas de listas *)
Theorem juntar_assoc : forall (lst1 lst2 lst3 : listanatural),
   (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3).

Proof.
   intros lst1 lst2 lst3. induction lst1 as [| h1 t1].
   reflexivity.
   simpl. rewrite -> IHt1. reflexivity.
Qed.

(* Reverte Lista *)
Fixpoint rev (lst : listanatural) : listanatural :=
   match lst with
   | [] => []
   | h :: t => rev t ++ [h]
   end.

Example teste_rev1:     rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example teste_rev2:     rev [] = [].
Proof. reflexivity. Qed.

(* Tamnho do inverso da lista é o mesmo que o original *)
Theorem rev_tamanho_primeira_tentativa : forall (lst : listanatural),
   tamanho (rev lst) = tamanho lst.

Proof.
   intros lst. induction lst as [| h t].
   - reflexivity.
   - simpl. rewrite <- IHt.
Abort.

(* Temos que provar um lema antes *)
Theorem juntar_tamanho : forall (lst1 lst2 : listanatural),
   tamanho (lst1 ++ lst2) = (tamanho lst1) + (tamanho lst2).

Proof.
   intros lst1 lst2. induction lst1 as [| h1 t1].
   - reflexivity.
   - simpl. rewrite IHt1. reflexivity.
Qed.

(* Agora provando *)
Theorem rev_tamanho : forall (lst : listanatural),
   tamanho (rev lst) = tamanho lst.

Proof.
   intros lst. induction lst as [| h t].
   - reflexivity.
   - simpl. rewrite -> juntar_tamanho.
     simpl. rewrite -> IHt. rewrite Nat.add_comm. (* importado da biblioteca *)
     reflexivity.
Qed.

(********************* Options **************************)

(* Função para retornar o n-ésimo elemento de uma lista*)
Fixpoint enesimo_ruim (lst : listanatural)(n : nat) : nat :=
   match lst with
   | [] => 42 (* Valor arbitrário *)
   | h :: t =>
       match n with
       | 0 => h
       | S k => enesimo_ruim t k
       end
   end.

(* Fazendo melhorias *)
(* A função acima é parcial e  não total, pois tem 
valores que não produzem saída válida. Para funções 
parciais, uma solução possível é criar um novo tipo,
que indica se tem ou não tem um valor como retorno *)
Inductive natoption : Type :=
   | Some (n : nat)  (* Se tiver algo para retornar*)
   | None.           (* Se não tiver nada para retornar*)

Fixpoint enesimo_erro (lst : listanatural) (n : nat) : natoption :=
   match lst with
   | [] => None
   | h :: t =>
        match n with
        | 0 => Some h
        | S k => enesimo_erro t k
        end
   end.

Example teste_enesimo_erro1 : enesimo_erro [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example teste_enesimo_erro2 : enesimo_erro [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example teste_enesimo_erro3 : enesimo_erro [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* Um casamento de padrão simultâneo deixa o código mais limpo *)
Fixpoint enesimo_erro' (lst : listanatural) (n : nat) : natoption :=
   match lst, n with
   | [], _ => None
   | h :: _, 0 => Some h
   | _ :: t, S k => enesimo_erro' t k
   end.

Example teste_enesimo_erro1' : enesimo_erro [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example teste_enesimo_erro2' : enesimo_erro [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example teste_enesimo_erro3' : enesimo_erro [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(********************** Partial Maps ********************)

(* Semelhante a dicionário *)
(* Mapas podem ser parciais, porque podem existir chaves que não são mapeadas *)

Inductive partial_map : Type :=
| Empty
| Binding (k : nat)(v : nat)(m : partial_map).

(* Fazer um update do binding da chave k para o valor v num mapa existente m *)
Definition update (k : nat)(v : nat)(m : partial_map) : partial_map :=
   Binding k v m.

(* Implementando uma função de busca *)
Fixpoint busca (k : nat)(m : partial_map) : natoption :=
   match m with 
   | Empty => None
   | Binding k2 v m' =>
       if k =? k2 then Some v else busca k m'
       end.

Theorem busca_update : forall (m : partial_map)(k v : nat),
   busca k (update k v m) = Some v.

Proof.
   intros m k v. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.