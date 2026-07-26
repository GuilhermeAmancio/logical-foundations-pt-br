
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
  

(********************* A tática apply ... with ... **********************)

(* O exemplo a seguir usa dois 'rewrites' em seguida par ir de [a;b] para
[e;f]. *)

Example trans_eq_exemplo : forall  (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2. Qed.

  (* Como esse é um padrão comum, gostariamos de considerá-lo um lema que 
  mostra, de uma vez por todas, o fato que a igualdade é transiiva *)

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.

Proof.
  intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

(* Agora, estamos aptos a usa trans_eq para provar o exemplo acima. 
No entanto, para fazer isso prcecisamos de um pequeno refinamento
da tática 'apply'. *)
Example trans_eq_exemplo' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f]->
     [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2.

(* Se simplesmente dissertermos ao Rocq para executar 'apply trans_eq' neste
ponto, ele conseguirá identificar (ao comparar o objetivo atual com a 
conclusão do lema) que deve instanciar X com [nat], x com [a,b] e z com [e,f]. 
No entanto, esse processo de correspondência não determina uma instanciação 
para y: precisamos fornecer uma explicitamente adicionando with (y:=[c,d]) 
à chamada do apply.*)

apply trans_eq with (y:=[c;d]).
apply eq1. apply eq2. Qed.

(* Na verdade, o nome y na cláusula with não é obrigatório, já que o Rocq 
geralmente é inteligente o suficiente para descobrir qual variável estamos 
instanciando. Em vez disso, poderíamos simplesmente escrever apply trans_eq 
with [c;d].
O Rocq também possui uma tática integrada chamada transitivity que cumpre
o mesmo propósito que aplicar trans_eq. A tática exige que declaremos a 
instanciação que queremos, assim como o apply with faz. *)
Example trans_eq_exemplo'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.

(* Exercício *)
Definition SubtraiDois (n : nat) : nat :=
   match n with
   | 0 => 0
   | S 0 => 0
   | S (S (n')) => n'
   end.

Example trans_eq_exercicio : forall (n m o p : nat),
     m = (SubtraiDois o) ->
     (n + p) = m ->
     (n + p) = (SubtraiDois o).

Proof.
  intros n m o p eq1 eq2.
  transitivity m.
  apply eq2. apply eq1. Qed.

(***************** As Táticas 'injection' e 'discriminate' *****************)

(* Relembre a definição de números naturais: *)     
Inductive nat : Type :=
   | O
   | S (n : nat).
  
(* É óbvio a partir desta definição que todo número possui uma de duas formas: 
ou ele é o construtor O, ou ele é construído aplicando o construtor S a outro 
número. Mas há mais nisso do que aparenta: implícitos na definição estão 
dois fatos adicionais:

  * O construtor S é injetivo (ou seja, um para um). Isto é, se S n = S m, 
    também deve ser verdade que n = m.

  * Os construtores O e S são disjuntos. Isto é, O não é igual a S n para 
  nenhum n.

Princípios semelhantes se aplicam a todo tipo definido indutivamente: todos 
os construtores são injetivos, e os valores construídos a partir de 
construtores distintos nunca são iguais. Para listas, o construtor cons é 
injetivo e a lista vazia nil é diferente de qualquer lista não vazia. 
Para booleanos, true e false são diferentes. (Como true e false não recebem 
argumentos, sua injetividade não faz diferença.) E assim por diante.

Podemos provar a injetividade de S usando a função pred definida em 
g_Naturais.v *)

Definition pred (n : nat) : nat :=
   match n with
   | O => O
   | S n' => n'
   end.


Theorem S_injetivo : forall (n m : nat),
  S n = S m ->
  n = m.
  
Proof.
  intros n m H1.
  assert (H2 : n = pred (S n)). 
  { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.