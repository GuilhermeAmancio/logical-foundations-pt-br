Require Import Arith.
Require Import Nat.

(* Provar o próximo teorema usando 'reflexivity não funciona, pois o n é um número arbitrário *)

Theorem add_0_r_primeiratentativa :
   forall n : nat,
   n + 0 = n.

Proof.
   intros n.
   simpl. (* Não faz nada *)
Abort.

Theorem add_0_r_segundatentativa :
   forall n : nat,
   n + 0 = n.

(* Mesmo fazendo vários destruct, não acontece nada, pois n pode ser arbitrariamente grande *)
Proof.
   intros n.
   destruct n as [| n'].
   reflexivity.
   simpl. (* Não faz nada *)
Abort.

(* Casos como esse podem ser resolvidos através de recursão *)
(* Queremos provar P(n) -- Primeiro, temos o subgoal P(0) -- Segundo, temos o subgoal P(n') -> P(S n') *)
Theorem add_0_r :
   forall n : nat,
   n + 0 = n.

Proof.
    intros n. induction n as [| n' IHn']. (* Nomes das variáveis a serem introduzidas como subgoal *)
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem menos_n_n:
   forall n: nat, minus n n = 0.

Proof.
   intros n. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercício *)
Theorem nult_0_r:
   forall n: nat, mult n 0 = 0.

Proof.
   intros n. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mais_n_Sm:
   forall n m: nat, S(n + m) = n + S(m).

Proof.
   intros n m. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comutativo:
   forall n m: nat, n + m = m + n.

Proof.
   intros n m. induction n as [| n' IHn'].
   - induction m as [| m' IHm'].
    + reflexivity.
    + simpl. rewrite <- IHm'. simpl. reflexivity.
   - simpl. rewrite IHn'. rewrite <- mais_n_Sm. reflexivity.
Qed.

Theorem add_associativo:
   forall n m p: nat, 
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercício *)

Fixpoint double (n : nat) :=
   match n with
   | 0 => 0
   | S n' => S (S (double n'))
   end.

Lemma double_mais:
   forall n, double n = n + n.

Proof.
   intros n. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. rewrite -> mais_n_Sm. reflexivity.
Qed.

(* Exercício *)

Theorem eqb_refl:
   forall n: nat, (n =? n) = true.

Proof.
   intros n. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite IHn'. reflexivity.
Qed.

(* Exercício -- Descrição alternativa de par de (S n) que funciona melhor para indução *)

Theorem negb_involutivo: (* Necessário mais tarde *)
   forall b : bool,
   negb (negb b) = b.

Proof.
   intros b. destruct b eqn: E.
   - reflexivity.
- reflexivity. Qed.

Theorem S_par:
   forall n: nat, even (S n) = negb (even n).

Proof.
   intros n. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - rewrite IHn'. simpl. rewrite negb_involutivo. reflexivity.

(* Provas dentro de provas *)
(* Usando a tática assertion *)

Theorem mult_0_mais : forall n m: nat,
   (n + 0 + 0) * m = n * m.

Proof.
   intros n m.
   assert (H: n + 0 + 0 = n). (* O nome da asserção é H. Queremos provar ess asserção *)
      { Set Printing Parentheses. rewrite add_comutativo. simpl. rewrite add_comutativo. reflexivity. }
       (* Set Printin Parentheses, faz com que o Rocq coloque toda a expressão entre parênteses *)
       rewrite -> H.
       reflexivity. Qed.

Theorem rearranjo_adicao_1tentativa : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   Set Printing Parentheses. rewrite add_comutativo. (* Não irá funcionar, pois vai trocar a ordem da soma mais exterior *)
Abort.

(* Para resolver isso, vamos usar assert *)
Theorem rearranjo_adicao : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   assert(H: n + m = m + n). (* Quando um rewrite não encontra a instância exata desejada, 'assert' a instância desejada, prove com um teorema auxiliar e rewrite com a hipótese introduzida pelo assert *)
   {
      rewrite add_comutativo. reflexivity.
   }
   rewrite H. reflexivity. Qed.

(* Usando a tática 'replace' *)
Theorem mult_0_mais' : forall n m : nat,
   (n + 0 + 0) * m = n * m.

Proof.
   intros n m.
   replace(n + 0 + 0) with n. (* Introduz dois subgoals -- um igual ao anterior substituindo pelo que desejamos, o outro para provar que o que acabou de ser introduzido é igual ao anterior *)
   - reflexivity.
   - rewrite add_comutativo. simpl. rewrite add_comutativo. reflexivity.
Qed.

Theorem rearranjo_adicao' : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   replace (n + m) with (m + n).
   - reflexivity.
   - rewrite add_comutativo. reflexivity.
Qed.

(* Provas Formais e Informais *)
(* Prova Formal - pode ser difícil para um humano compreender *)
Theorem add_associativo' : forall n m p: nat,
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [| n' IHn']. reflexivity.
   simpl. rewrite IHn'. reflexivity.  Qed.

(* Para facilitar o entendimento, comentários e bullets (-) podem ser usados para tornar semelhante a uma prova informal, que será mais facilmente compreendida pelo leitor *)
Theorem add_associativo'' : forall n m p: nat,
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [| n' IHn']. 
   - (* n = 0 *)
   reflexivity.
   - (* n = S n' *)
   simpl. rewrite IHn'. reflexivity.  Qed.

(* Uma prova poderia ser escrite em linguagem natural como:
   Teorema: Para qualquer n, m e p.
        n + (m + p) = (n + m) + p.
   Prova : Por indução de n.
   -Primeiro, suponha que n = 0. Devemos provar que
      0 + (m + p) = (0 + m) + p.
      Isso segue da definição de + (soma).
   - Depois, suponha que n = S n', onde
      n' + (m + p) = (n' + m) + p.
   Nós devemos mostrar agora que 
      (S n') + (m + p) = ((S n') + m) + p.
   Pela definição de +, segue que
      S(n' + (m + p)) = S((n' + m) + p),
   que é imediato da hipótese de indução. Qed.
 *)

 (* Exercício *)

 (* 
    Prova: Por indução em n e, em cada caso, por indução em m.

    Caso n = 0:
    Devemos mostrar que 0 + m = m + 0. Fazemos indução em m:

        Se m = 0:
        Devemos mostrar que 0 + 0 = 0 + 0, o que é imediato por reflexividade.

        Se m = S m', com a hipótese de indução (0 + m' = m' + 0):
        Devemos mostrar que 0 + (S m') = (S m') + 0.
        Por simplificação e usando a hipótese de indução de m, a igualdade
        se mantém, completando o caso n = 0.

    Caso n = S n', com a hipótese de indução (n' + m = m + n'):
    Devemos mostrar que (S n') + m = m + (S n').
    Por simplificação e reescrita usando a hipótese de indução de n,
    junto com o lema mais_n_Sm para ajustar o sucessor, o objetivo
    é reduzido a uma identidade.
    Isso encerra todos os casos. Qed.
    *)


Theorem add_rearranjo3 : forall n m p: nat,
   n + (m + p) = m + (n + p).

Proof.
    intros n m p.
    rewrite add_associativo.
    replace ( n + m) with (m + n).
    - rewrite add_associativo. reflexivity.
    - rewrite add_comutativo. reflexivity.
Qed.

(* Exercício : Agora prove a comutatividade da multiplicação. Você provavelmente vai querer olhar para (ou definir e provar) um teorema "helper" para ser usado nessa prova. Dica: o que é n × (1 + k)?*)

(* Helper 1 *)
Lemma mul_0_r : forall n : nat,
  n * 0 = 0.

Proof.
   intros n.
   induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed. 

(* Helper 2 *)
Lemma mul_S_r : forall n k : nat,
  n * S k = n * k + n.

Proof.
  intros n k.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. replace (S k + (n' * k + n')) with (k + n' * k + S n').
  rewrite add_associativo.
  rewrite mais_n_Sm. 
  reflexivity.

  rewrite add_associativo.
  simpl.
  rewrite mais_n_Sm.
  reflexivity.
Qed.

Theorem mul_comutativo: forall m n: nat,
   m * n = n * m.

Proof.
   intros m n.
   induction m as [| m' IHm'].
   simpl. rewrite mul_0_r. reflexivity.
   simpl. rewrite mul_S_r. rewrite add_comutativo. rewrite IHm'. reflexivity.
Qed. 

   
   

     
      