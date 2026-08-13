Require Import List.
Import ListNotations.
Require Import Nat.

(* Funções de Alta Ordem *)
(* Funções que manipulam outras funções*)

Definition facaisso3vezes {X : Type} (f : X -> X) (n : X) : X :=
   f (f (f n)).

Check @facaisso3vezes : forall X : Type, (X -> X) -> X -> X.

(* Usando a função vista inicialmente no capítulo inicial *)
Definition SubtraiDois (n : nat) : nat :=
   match n with
   | 0 => 0
   | S 0 => 0
   | S (S (n')) => n'
   end.

Example teste_facaisso3vezes: facaisso3vezes SubtraiDois 9 = 3.
Proof. reflexivity. Qed.

Example teste_facaisso3vezes': negb true = false.
Proof. reflexivity. Qed.

(* Filter *)
(* A função filter serve para filtrar elementos de uma lista que satisfazem 
um predicado *)
Fixpoint filter {X : Type} (teste : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if teste h then h :: (filter teste t)
    else filter teste t
  end.

Example teste_filter1: filter Nat.even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition tamanho_e_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example teste_filter2:  filter tamanho_e_1
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].


Proof. reflexivity. Qed.

Definition contanumerosimpares' (l : list nat) : nat :=
  length (filter odd l).

Example teste_contanumerosimpares'1: contanumerosimpares' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_contanumerosimpares'2: contanumerosimpares' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_contanumerosimpares'3: contanumerosimpares' nil = 0.
Proof. reflexivity. Qed.

(* Funções Anônimas *)
(* Não precisa dar um nome para funções *)
Example teste_anon_fun':
  facaisso3vezes (fun n => n * n) 2 = 256. (* Função que recebe n e dá n * n *)

Proof. reflexivity. Qed.

Example teste_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].

Proof. reflexivity. Qed.

(* Outras duas funções de alta ordem importantes são Map e Fold *)

(* Map *)
(* Transforma todos os elementos de uma coleção *)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example teste_map1: map (fun x => 3 + x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example teste_map2: map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example teste_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Usando map com options *)
 Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* Fold *)
(* Combina elementos de uma lista em um único valor *)
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* fold é similar com outra função chamada reduce de map/reduce *)

Check (fold andb) : list bool -> bool -> bool.

Example fold_exemplo1 :
   fold mult [2;3;4] 1 = 24. (* 2 * ( 3 * ( 4 * 1)) *)
Proof. reflexivity. Qed.

Example fold_exemplo2 :
   fold andb [true;true;false;true] true = false. 
   (* T && ( T && (F && ( T && T))) *)
Proof. reflexivity. Qed.

Example fold_exemplo3 :
   fold (@app nat) [[1];[];[2;3];[4];[]] [] = [1;2;3;4].
   (* [1] ++ ([] ++ ([2;3] ++ ([4] ++ []))) *)
Proof. reflexivity. Qed.

(* Funções que constroem outras funções *)
Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true. (* true sempre vai ser o que vai ser passado de volta *)

Example constfun_examplo1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_examplo2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* Funções com dois ou mais argumentos são, na verdade, funções que tomam 
um argumento e retornam uma função *)
Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example teste_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example teste_plus3' : facaisso3vezes plus3 0 = 9.
Proof. reflexivity. Qed.
Example teste_plus3'' : facaisso3vezes (plus 3) 0 = 9.
Proof. reflexivity. Qed.