(* Definindo tipos booleanos*)

(* true e false são chamados  de construtores do tipo Inductive bool *)
Inductive bool : Type :=
 | true
 | false.

 (* Definindo algumas funções booleanas que já estão definidas na biblioteca do Coq/Rocq *)

(* Negação *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Conjunção *)
Definition conjuncaob (b1:bool)(b2:bool) : bool := (* Nesse caso há mais de um argumento *)
   match b1 with
   | true => b2 (*caso b1 seja verdadeiro, o resultado da conjunção vai ser o valor lógico de b2*)
   | false => false
   end.

(* Disjunção *)
Definition disjuncaob (b1 b2 : bool) : bool := (* Outra síntaxe para funções com mais de um argumento*)
   match b1 with
   | true => true
   | false => b2 (* Se b1 for falso, o resultado será o valor lódgico de b2*)
   end.

(* Temos que provar os exemplos -- simpl. simplifica o lado esquerdo - reflixivity é a propriedade de reflexividade - quando não houver mais nenhum subgoal usamos Qed e os testes estão definidos*)

Example teste_disjuncaob1: (disjuncaob true false) = true.
Proof. simpl. reflexivity. Qed.
Example teste_disjuncaob2: (disjuncaob false false) = false.
Proof. simpl. reflexivity. Qed.
Example teste_disjuncaob3: (disjuncaob false true) = true.
Proof. simpl. reflexivity. Qed.
Example teste_disjuncaob4: (disjuncaob true false) = true.
Proof. simpl. reflexivity. Qed.

(* Definindo novas notações simbólicas para definições que já existem *)
Notation "x && y" := (conjuncaob x y).
Notation "x || y" := (disjuncaob x y).

(* Um exemplo com a nova notação *)
Example teste_disjuncaob5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Podemos definir funções com 'if' ao invés de casamento de padrões (match) *)
Definition negb' (b:bool) : bool :=
   if  b then false (* Imagine como o operador ternário*)
   else true.

Definition conjuncaob' (b1:bool) (b2:bool) : bool :=
   if b1 then b2
   else false.

Definition disjuncaob' (b1:bool) (b2:bool) : bool :=
   if b1 then true
   else b2.


(* Resolução de exercícios*)
Definition nandb (b1:bool)(b2:bool) : bool :=
   match b1 with
   |false => true
   |true =>
      match b2 with
      |false => true
      |true => false
      end
   end.
 
Example teste_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example teste_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example teste_nandb3 : (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example teste_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.