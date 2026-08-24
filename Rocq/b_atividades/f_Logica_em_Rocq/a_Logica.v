(* LÓGICA *)
(* LÓGICA EM ROCQ*)

(* Agora já vimos muitos exemplos de afirmações factuais (ou seja, 
proposições) e maneiras de apresentar evidências de sua verdade (provas). 
Em particular, trabalhamos extensivamente com proposições de igualdade 
(e1 ​= e2​), implicações (P → Q) e proposições quantificadas (∀x, P). 
Neste capítulo, veremos como o Rocq pode ser usado para realizar outras 
formas familiares de raciocínio lógico.

Antes de mergulhar nos detalhes, precisamos falar um pouco sobre o status 
das declarações matemáticas no Rocq. O Rocq é uma linguagem tipada, o que 
significa que toda expressão sensata tem um tipo associado. As afirmações 
lógicas não são exceção: qualquer declaração que possamos tentar provar no 
Rocq tem um tipo, a saber, Prop, o tipo das proposições. Podemos ver isso 
com o comando Check: *)

Check (forall n m : nat, n + m = m + n) : Prop.

(* Note que todas as proposições sintaticamente bem formadas têm o tipo 
Prop no Rocq, independentemente de serem verdadeiras ou não.

Simplesmente ser uma proposição é uma coisa; ser provável é uma coisa 
totalmente diferente! *)
Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

(* De fato, as proposições não têm apenas tipos — elas são entidades de p
rimeira classe que podem ser manipuladas exatamente da mesma forma que 
qualquer outra coisa no mundo do Rocq.

Até agora, vimos um lugar principal onde as proposições podem aparecer: em 
declarações de Theorem (além de Lemma e Example). *)
Theorem plus_2_2_is_4 :
  2 + 2 = 4.

Proof. reflexivity. Qed.

(* Mas as proposições podem ser usadas de outras maneiras. Por exemplo,
 podemos dar um nome a uma proposição usando uma Definition, assim como 
 damos nomes a outros tipos de expressões. *)
Definition afirmacao_soma : Prop := 2 + 2 = 4.
Check afirmacao_soma : Prop.

(* Podemos usar esse nome posteriormente em qualquer situação onde uma 
proposição seja esperada — por exemplo, como a afirmação em uma declaração 
de Theorem. *)
Theorem afirmacao_soma_e_verdade :
  afirmacao_soma.

Proof. reflexivity. Qed.

(* Também podemos escrever proposições parametrizadas — ou seja, funções 
que aceitam argumentos de algum tipo e retornam uma proposição.

Por exemplo, a função a seguir recebe um número e retorna uma proposição 
afirmando que esse número é igual a três: *)
Definition e_tres (n : nat) : Prop :=
  n = 3.

Check e_tres : nat -> Prop.

(* No Rocq, diz-se que funções que retornam proposições definem 
propriedades de seus argumentos.

Por exemplo, aqui está uma propriedade (polimórfica) que define a noção 
familiar de uma função injetiva. *)
Definition injetivo {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injetivo S.

Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(* O operador de igualdade familiar = é uma função (binária) que retorna um 
Prop.

A expressão n = m é uma forma abreviada para eq n m (definida na biblioteca 
padrão do Rocq usando o mecanismo de Notação). 

Como eq pode ser usado com elementos de qualquer tipo, ele também é 
polimórfico: *)

Check @eq : forall A : Type, A -> A -> Prop.

(* (Note que escrevemos @eq em vez de eq: o argumento de tipo A para eq é 
declarado como implícito, e precisamos desativar a inferência desse argumento 
implícito para ver o tipo completo de eq.) *)

(*************************** Conectivos Lógicos *****************************)

(******************************** Conjunção *******************************)
(* A conjunção, ou 'e' lógico, das proposições A e B é escrita como A ∧ B;
ela representa a afirmação de que tanto A quanto B são verdadeiros. *)

Notation "A /\ B" := (and A B) : type_scope.
Example e_exemplo : 3 + 4 = 7 /\ 2 * 2 = 4.

(* Para provar uma conjunção, comece com a tática split. Isso gerará duas 
submetas, uma para cada parte da afirmação: *)
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(* Para quaisquer proposições A e B, se assumirmos que A e B são verdadeiras 
individualmente, podemos concluir que A ∧ B também é verdadeira. A 
biblioteca do Rocq fornece uma função 'conj' que faz isso *)
Check @conj : forall A B : Prop, A -> B -> A /\ B.

(* Como a aplicação de um teorema com hipóteses a um objetivo tem o efeito 
de gerar tantas submetas quantas forem as hipóteses desse teorema, podemos 
aplicar conj para alcançar o mesmo efeito que a tática split. *)
Example e_exemplo' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(* Exercício *)
Example adicao_e_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.

Proof.
   intros n m H.
   apply conj.
   - destruct n.
     + reflexivity.
     + discriminate H.
   - destruct m.
     + destruct n.
       * reflexivity.
       * discriminate H.
     + destruct n.
       * discriminate H.
       * discriminate H.
Qed.

(* Por enquanto é isso sobre provar proposições conjuntas. Para ir na 
direção oposta — isto é, usar uma hipótese conjuntiva para ajudar a provar 
outra coisa — podemos usar nossa boa e velha tática destruct.

Quando o contexto atual da prova contém uma hipótese H da forma A ∧ B, 
escrever destruct H as [HA HB] removerá H do contexto e a substituirá por 
duas novas hipóteses: HA, afirmando que A é verdadeira, e HB, afirmando que 
B é verdadeira. *)
    
Lemma e_exemplo2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.

Proof.
  (* TRABALHADO EM SALA *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
      
(* Como de costume, também podemos destruir H logo no momento em que a 
introduzimos, em vez de introduzi-la primeiro e depois destruí-la: *)

Lemma e_exemplo2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.

Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* Você deve estar se perguntando por que nos demos ao trabalho de empacotar 
as duas hipóteses n = 0 e m = 0 em uma única conjunção, já que também 
poderíamos ter enunciado o teorema com duas premissas separadas: *)

Lemma e_exemplo2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.

Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* Para este teorema específico, ambas as formulações funcionam bem. Mas é 
importante entender como trabalhar com hipóteses conjuntivas porque as 
conjunções frequentemente surgem de etapas intermediárias em provas, 
especialmente em desenvolvimentos maiores. Aqui está um exemplo simples: *)

 Lemma e_exemplo3 :
  forall n m : nat, n + m = 0 -> n * m = 0.

Proof.
  intros n m H.
  apply adicao_e_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(* Outra situação comum é que sabemos A ∧ B, mas em algum contexto precisamos 
apenas de A ou apenas de B. Nesses casos, podemos fazer um destruct 
(possivelmente de forma implícita, como parte de um intros) e usar um padrão 
de sublinhado (_) para indicar que a parte da conjunção que não precisamos 
deve simplesmente ser descartada. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.

Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.

(* Exercício *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.

Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HQ].
  apply HQ. Qed.

(* Finalmente, às vezes precisamos reorganizar a ordem das conjunções e/ou 
o agrupamento de conjunções de várias vias (múltiplas). Podemos ver isso em 
ação nas provas dos seguintes teoremas de comutatividade e associatividade: *)

Theorem e_comut : forall P Q : Prop,
  P /\ Q -> Q /\ P.

Proof.
  intros P Q [HP HQ].
  split.
    - (* esquerda *) apply HQ.
    - (* direita *) apply HP. Qed.

(* Exercício *)
(* Na prova de associatividade a seguir, note como o padrão de intros 
aninhado decompõe a hipótese H : P ∧ (Q ∧ R) em HP : P, HQ : Q e HR : R. 
Termine a prova. *)
Theorem e_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.

Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

(* A notação infixa ∧ é, na verdade, apenas uma notação simplificada 
para and A B. Ou seja, and é um operador do Rocq (Coq) que recebe duas 
proposições como argumentos e produz uma proposição. *)
Check and : Prop -> Prop -> Prop.
  
(******************************** Disjunção *******************************)