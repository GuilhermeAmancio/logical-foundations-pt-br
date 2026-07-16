
Require Import List.
Import ListNotations.
Import List.

(* Tática Apply *)

(* Frequentemente encontramos situações onde o goal a ser provado é 
exatamente o mesmo que alguma hipótese no contexto ou um lema provado
anteriormente *)

Theorem bobinho1 : forall (n m : nat),
   n = m -> n = m.
   intros n m eq.
   apply eq. Qed.

(* A tática apply também funciona com hipóteses e lemas condicionais: 
se a sentença sendo aplicada for uma implicação, então as premissas 
dessa implicação serão adicionadas a lista de subgoals a serem provadas. 
apply também funciona com hipóteses condicionais: *)
Theorem bobinho2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

(* O comando apply H faz o Rocq deduzir automaticamente os valores das 
variáveis universais de H ao comparar a conclusão da regra com o seu 
objetivo atual. *)
Theorem bobinho2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercício 
Complete a seguinte prova usando apenas intros e apply. *)
Theorem bobinho_ex : forall p,
  (forall n, Nat.even n = true -> Nat.even (S n) = false) ->
  (forall  n, Nat.even n = false -> Nat.odd n = true) ->
  Nat.even p = true -> Nat.odd (S p) = true.
Proof.
  intros n p q eq1.
  apply q. apply p. apply eq1.
Qed.

(* Para usar a tática apply, a (conclusão do) fato sendo aplicado deve 
corresponder exatamente ao objetivo (goal) atual (talvez após alguma 
simplificação), por exemplo, o apply não funcionará se os lados esquerdo e 
direito de uma igualdade estiverem invertidos. *)
Theorem bobinho3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.

(* Aqui não podemos usar 'apply' diretamente *)
Fail apply H.

(* ...mas nós podemos usar a tática 'symmetric', que troca o lado esquerdo e
direito de uma igualdade em um goal. *)
symmetry. apply H. Qed.

(* Exercício
Você pode usar o apply com teoremas definidos anteriormente, não apenas com
hipóteses que já estão no seu contexto. Use o comando Search para encontrar
um teorema previamente definido sobre rev no módulo de listas (Lists). 
Use esse teorema como parte da sua solução (que é relativamente curta) para 
este exercício. Você não precisa usar indução.*)

Theorem rev_exercicio1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  Search rev inside Coq.Lists.List.
  rewrite H.
  symmetry.
  apply List.rev_involutive.
Qed.

(* Exercício: 1 estrela
Explique brevemente a diferença entre as táticas apply e rewrite. 
Quais são as situações em que ambas podem ser aplicadas de forma útil?*)

(* o rewrite funciona como um buscar e substituir que usa uma igualdade 
(A = B) para trocar um termo pelo outro no objetivo, 
enquanto o apply realiza um raciocínio lógico inverso (de trás para frente) 
usando uma implicação (P -> Q): se o seu objetivo atual é exatamente a 
conclusão Q, a tática o substitui pela premissa P que ainda precisa ser 
provada (ou fecha o objetivo na hora, caso a hipótese seja um fato direto 
P). *)
  