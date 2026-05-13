(* Definindo número naturais*)

Module ZonaDosNaturais.

(* Representando os números naturais por sistema unário*)
Inductive nat : Type :=
   | O 
   | S (n : nat).

(* 0 é representado por [O], 1 por [S 0], 2 por [S (S 0)], ...*)

(* Outra maneira de representar os números naturais, com lógica semelhante*)
Inductive nat' : Type :=
   | parar
   | marcar (foo: nat').

(* Função de predecessor*)
Definition pred (n : nat) : nat :=
   match n with
   | O => O
   | S n' => n'
   end.

End ZonaDosNaturais. (* Fim dos módulos dos naturais*)

Check (S (S ( S ( S (O))))).

(* Função que dado n tem como saída n - 2 *)
Definition SubtraiDois (n : nat) : nat :=
   match n with
   | 0 => 0
   | S 0 => 0
   | S (S (n')) => n'
   end.

Compute(SubtraiDois 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check SubtraiDois : nat -> nat.

(* Recursão -- Uso de 'Fixpoint' para indicar função recursiva *)

Fixpoint NumeroPar (n : nat) : bool :=
   match n with
   | O => true    (* Caso Base *)
   | S O => false (* Caso Base*)
   | S (S n') => NumeroPar n' (* Chama recursivamente *)
   end.

Definition NumeroImpar (n : nat) : bool :=
   negb (NumeroPar n).

Example teste_impar1 : NumeroImpar 1 = true.
Proof. simpl. reflexivity. Qed.

Example teste_impar2 : NumeroImpar 4 = false.
Proof. simpl. reflexivity. Qed.

Module ZonaDosNaturais2.
Fixpoint Adicao (n : nat) (m : nat) : nat :=
   match n with
   | O => m
   | S n' => S (Adicao n' m)
   end.

Compute (Adicao 3 2).

Fixpoint Multiplicacao (n m : nat) : nat :=
   match n with
   | O => O 
   | S n' => Adicao m (Multiplicacao n' m)
   end.

Example teste_multiplicacao1: (Multiplicacao 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint Subtracao (n m : nat) : nat :=
   match n, m with
   | O , _ => O 
   | S _ , O => n
   | S n' , S m' => Subtracao n' m'
   end. 

End ZonaDosNaturais2.

Fixpoint expoente (base potencia : nat) : nat :=
   match potencia with
   | O => S O
   | S p => mult base (expoente base p)
   end.

(* Exercício *) 
Fixpoint Fatorial (n : nat) : nat :=
   match n with
   | O => S(O)
   | S n' => mult (S n') (Fatorial(n'))
   end.

Example teste_fatorial1 : (Fatorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example teste_fatorial2 : (Fatorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* Mudando a notação*)
Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.

Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((O + 1) + 1) : nat.

(* Função para verificar se n é igual a m*)
Fixpoint igualb (n m : nat) : bool :=
   match n with 
   | O => match m with
          | O => true
          | S m' => false
          end
   | S n' => match m with
             | O => false
             | S m' => igualb n' m'
             end
   end.
   
(* Função para verificar se n é menor ou igual a m *)
Fixpoint menorigualb (n m : nat) : bool :=
   match n with 
   | O => true
   | S n' =>
      match m with
      | O => false
      | S m' => menorigualb n' m'
      end   
   end.

Example teste_menorigualb1: menorigualb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example teste_menorigualb2: menorigualb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example teste_menorigualb3: menorigualb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (igualb x y)(at level 70): nat_scope.
Notation "x <=? y" := (menorigualb x y)(at level 70): nat_scope.

Example teste_menorigual3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Obs: O símbolo '=' é uma afirmação lógica, uma proposição. Já o símbolo '=?' é uma expressão booleana cujo valor pode ser computado *)

(* Exercício -- ltb = less-than b = menor que b*)
Definition ltb (n m : nat) : bool :=
   if n =? m then
     if n <=? m then
      true
      else 
       false
    else
false.

Notation "x <? y" := (ltb x y)(at level 70) : nat_scope.

Example teste_ltb1: (ltb 2 2) = false.
Proof. simp. reflexivity. Qed.

Example teste_ltb2: (ltb 2 4) = true.
Proof. simp. reflexivity. Qed.

Example teste_ltb3: (ltb 4 2) = false.
Proof. simp. reflexivity. Qed.





