(* Neste capítulo, examinamos de forma mais aprofundada como usar o Rocq como uma 
ferramenta para estudar outras coisas. Nosso estudo de caso é uma linguagem de programação 
imperativa simples chamada Imp, que incorpora um pequeno fragmento central de linguagens 
convencionais e populares, como C e Java. Aqui está uma função matemática familiar 
escrita em Imp: 

Z := X;
Y := 1;
while Z ≠ 0 do
  Y := Y × Z;
  Z := Z - 1
end

Concentramo-nos aqui em definir a sintaxe e a semântica do Imp; mais tarde, em 
Programming Language Foundations (Software Foundations, volume 2), desenvolvemos uma teoria 
de equivalência de programas e introduzimos a Lógica de Hoare, uma lógica popular para 
raciocinar sobre programas imperativos. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
Require Import LFPTBR.h_Mapas_Totais_e_Parciais.a_Mapas_Totais_e_Parciais.

(*************************** Expressões Aritméticas e Booleanas **************************)

(* Apresentaremos o Imp em três partes: primeiro, uma linguagem central de expressões 
aritméticas e booleanas; depois, uma extensão destas com variáveis; e, por fim, uma 
linguagem de comandos que inclui atribuição, condicionais, sequenciamento e loops. *)

(*** Sintaxe ***)

Module AExp.

(* Estas duas definições especificam a sintaxe abstrata de expressões aritméticas e 
booleanas. *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* Neste capítulo, nós vamos basicamente omitir a tradução da sintaxe concreta que um 
programador realmente escreveria para estas árvores de sintaxe abstrata — o processo que, 
por exemplo, traduziria a string ''1 + 2 × 3'' para a AST. 
                APlus (ANum 1) (AMult (ANum 2) (ANum 3)). 
                
O capítulo opcional ImpParser desenvolve um analisador léxico e um parser simples que 
podem realizar essa tradução. Você não precisa entender aquele capítulo para entender 
este, mas, se ainda não fez um curso onde essas técnicas são abordadas (por exemplo, um 
curso de compiladores), pode querer dar uma olhada rápida nele. Para comparação, aqui 
está uma gramática convencional em BNF (Backus-Naur Form) que define a mesma sintaxe 
abstrata:
      a := nat
        | a + a
        | a - a
        | a × a

       b := true
        | false
        | a = a
        | a ≠ a
        | a ≤ a
        | a > a
        | ¬b
        | b && b
        
Comparada à versão do Rocq acima... 

  - A BNF é mais informal — por exemplo, ela dá algumas sugestões sobre a sintaxe de 
    superfície das expressões (como o fato de a operação de adição ser escrita com um + 
    infixo), enquanto deixa outros aspectos da análise léxica e sintática (como a 
    precedência relativa de +, - e ×, o uso de parênteses para agrupar subexpressões, etc.) 
    não especificados. Alguma informação adicional — e inteligência humana — seria 
    necessária para transformar essa descrição em uma definição formal, por exemplo, para 
    implementar um compilador. 

    A versão do Rocq consistentemente omite todas essas informações e se concentra 
    apenas na sintaxe abstrata.

  - Por outro lado, a versão BNF é mais leve e fácil de ler. Sua informalidade a torna 
    flexível, o que é uma grande vantagem em situações como discussões no quadro-negro, 
    onde transmitir ideias gerais é mais importante do que fixar cada detalhe com 
    precisão. 
    
    De fato, existem dezenas de Notações Estilo-BNF e as pessoas alternam livremente 
    entre elas — geralmente sem se incomodar em dizer qual tipo de BNF estão usando, 
    porque não há necessidade: uma compreensão informal aproximada e prática 
    (''grosseira, mas pronta'') é tudo o que importa.

É bom estar familiarizado com ambos os tipos de notação: as informais para a comunicação 
entre humanos e as formais para a realização de implementações e provas. *)

(*** Avaliação ***)

(* Avaliar uma expressão aritmética produz um número. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example teste_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(* Analogamente, a avaliação de uma expressão booleana produz um resultado booleano. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(*** Otimização ***)

(* Ainda não definimos muito, mas podemos já tirar proveito das definições existentes. Suponha 
que definamos uma função que receba uma expressão aritmética e a simplifique levemente, 
substituindo cada ocorrência de 0 + e (isto é, (APlus (ANum 0) e)), por apenas e.*)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(* Para ganhar confiança de que nossa otimização está fazendo a coisa certa, podemos 
testá-la em alguns exemplos e verificar se a saída parece correta. *)

Example teste_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(* Mas se queremos ter certeza de que a otimização está correta — isto é, que avaliar uma
expressão otimizada sempre produz o mesmo resultado que a original — devemos prová-la! *)
Theorem optimize_0plus_corretude: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.

(************************************* Automação do Rocq *************************************)

(* A quantidade de repetição nesta última prova é um pouco irritante. E se tanto a linguagem 
das expressões aritméticas quanto a otimização cuja corretude fosse significativamente mais 
complexa, isso começaria a ser um problema sério. 

Até agora, temos feito todas as nossas provas usando apenas um pequeno punhado de táticas do
Rocq e ignorando completamente suas poderosas facilidades para construir partes das provas 
automaticamente. Esta seção introduz algumas dessas facilidades, e veremos mais ao longo dos
próximos capítulos. Aproveitar-se delas exigirá algum esforço — a automação do Rocq é uma
ferramenta poderosa — mas permitirá que ampliemos nossos esforços para definições mais 
complexas e propriedades mais interessantes sem nos deixarmos esmagados por detalhes chatos,
repetitivos e de baixo nível *)

(*** Tacticals ***)

(* Tacticals é o termo do Rocq para táticas que aceitam outras táticas como argumentos — 
'táticas de ordem superior', se quiser dizer assim. *)

(** O Tactical try **)

(* Se T for uma tática, então try T é uma tática exatamente igual a T, exceto pelo fato de que, 
se T falhar, try T simplesmente não faz absolutamente nada com sucesso (em vez de falhar). *)

Theorem bobinho1 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* A reflexividade pura teria falhado. *)
  apply HP. (* Ainda podemos concluir a prova de outra forma. *)
Qed.

Theorem bobinho2 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* Isso faz apenas a reflexividade. *)
Qed.

(* Não há muita razão para usar o try em provas totalmente manuais como estas, mas ele é muito 
útil para fazer provas automatizadas em conjunto com o tactical ;, que mostraremos a seguir. *)

(** O Tactical ; (Forma Simples) **)

(* Na sua forma mais comum, o tactical ; recebe duas táticas como argumentos. 
A tática composta T;T' primeiro executa T e depois executa T' em cada submeta 
gerada por T. 

Por exemplo, considere o seguinte lema trivial: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Deixa duas submetas, que são resolvidas de forma idêntica...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(* Podemos simplificar esta prova usando o tactical ; : *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* faça o destruct da meta atual *)
  destruct n;
  (* depois aplique simpl em cada submeta resultante *)
  simpl;
  (* e aplique reflexivity em cada submeta resultante *)
  reflexivity.
Qed.

(* Usando try e ; juntos, podemos eliminar a repetição na prova que estava nos 
incomodando há pouco *)

Theorem optimize_0plus_corretude': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* A maioria dos casos decorre diretamente da IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* mas os casos restantes -- ANum e APlus -- 
       são diferentes: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Novamente, a maioria dos casos decorre diretamente da IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* O caso interessante, no qual o try... 
       não faz nada, é quando e1 = ANum n. Neste 
       caso, precisamos aplicar destruct em n (para ver
        se a otimização se aplica) e reescrever com a 
        hipótese de indução. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity. Qed.

(* Especialistas em Rocq frequentemente usam esse idioma ...; try... após uma 
tática como induction para cuidar de vários casos semelhantes de uma só vez. 
De fato, essa prática tem um análogo em provas informais. Por exemplo, aqui 
está uma prova informal do teorema de otimização que corresponde à estrutura 
da formal: 

Teorema: Para todas as expressões aritméticas a,
    aeval (optimize_0plus a) = aeval a.
    
Prova: Por indução em a. A maioria dos casos decorre diretamente da IH. 
Os casos restantes são os seguintes:

    - Suponha que a = ANum n para algum n. Devemos mostrar que:
                    aeval (optimize_0plus (ANum n)) = aeval (ANum n).
      Isso é imediato a partir da definição de optimize_0plus.
      
    - Suponha que a = APlus a1 a2 para alguns a1 e a2. Devemos mostrar que:
                    aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).
      Considere as formas possíveis de a1. Para a maioria delas, optimize_0plus 
      simplesmente chama a si mesma recursivamente para as subexpressões e 
      reconstrói uma nova expressão da mesma forma que a1; nesses casos, o 
      resultado decorre diretamente da IH. 
      
      O caso interessante é quando a1 = ANum n para algum n. Se n = 0, então:
                  optimize_0plus (APlus a1 a2) = optimize_0plus a2
      e a IH para a2 é exatamente o que precisamos. Por outro lado, se n = S n' 
      para algum n', então, novamente, optimize_0plus simplesmente chama a si 
      mesma recursivamente, e o resultado decorre da IH. ☐

No entanto, esta prova ainda pode ser aprimorada: o primeiro caso (para 
a = ANum n) é muito trivial — ainda mais trivial do que os casos que dissemos 
simplesmente decorrer da IH — e, mesmo assim, optamos por escrevê-lo por 
extenso. Seria melhor e mais claro omiti-lo e apenas dizer, no início, ''A 
maioria dos casos é imediata ou decorre diretamente da IH. O único caso 
interessante é o de APlus...''. Podemos fazer a mesma melhoria em nossa prova 
formal também. Eis como ela fica: *)

Theorem optimize_0plus_corretude'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* A maioria dos casos decorre diretamente da IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... ou são imediatos por definição *)
    try reflexivity.
  (* O caso interessante é quando a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(** O Tactical ; (Forma Geral) **)

(* O tactical ; também possui uma forma mais geral do que a simples T;T' que 
vimos acima. Se T, T_1, ..., T_n são táticas, então: 
      T; [T1 | T2 | ... | Tn]
é uma tática que primeiro executa T e, em seguida, executa T1 no primeiro 
subobjetivo gerado por T, executa T2 no segundo subobjetivo, e assim por 
diante.

Portanto, T;T' é apenas uma notação especial para o caso em que todos os 
T_i são a mesma tática; ou seja, T;T' é uma abreviação para:
          T; [T' | T' | ... | T']  *)

(** O tactical repeat **)

(* O tactical repeat pega outra tática e continua aplicando-a até que ela falhe ou até que seja 
bem-sucedida, mas sem fazer nenhum progresso. 

Aqui está um exemplo provando que 10 está em uma lista longa usando o repeat.*)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(* A tática repeat T nunca falha: se a tática T não se aplica ao objetivo original, então o 
repeat é bem-sucedido sem alterar o objetivo (ou seja, ele se repete zero vezes). *)
Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(* A tática repeat T não tem limite superior para o número de vezes que aplica T. Se T for uma 
tática que sempre é bem-sucedida (e faz progresso), então o repeat T entrará em loop infinito. *)
Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Descomente a próxima linha para ver o loop infinito ocorrer. Em seguida, você precisará 
     interromper o Rocq para que ele volte a responder. (No Proof General, C-c C-c faz isso.) *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

(* Espere — nós acabamos de escrever um loop infinito no Rocq?!?!

Mais ou menos. Enquanto a avaliação na linguagem de termos do Rocq, a Gallina, tem garantia de 
término, a avaliação de táticas não tem. No entanto, isso não afeta a consistência lógica do 
Rocq, já que o trabalho do repeat e de outras táticas é guiar o Rocq na construção de provas;
se o processo de construção diverge (ou seja, não termina), isso significa apenas que falhamos
em construir uma prova, e não que construímos uma prova ruim. *)

(* Exercício *)
(* Como a transformação optimize_0plus não altera o valor das aexps, devemos ser capazes de 
aplicá-la a todas as aexps que aparecem em uma bexp sem alterar o valor da bexp. Escreva uma 
função que realize essa transformação em bexps e prove que ela é correta. Use os tacticals que 
acabamos de ver para tornar a prova o mais curta e elegante possível. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
 match b with
   | BTrue => BTrue
   | BFalse => BFalse
   | BEq a1 a2 => BEq (optimize_0plus a1)(optimize_0plus a2)
   | BNeq a1 a2 => BNeq (optimize_0plus a1)(optimize_0plus a2)
   | BLe a1 a2 => BLe (optimize_0plus a1)(optimize_0plus a2)
   | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
   | BNot b1 =>  BNot (optimize_0plus_b b1)
   | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
   end.

Example optimize_0plus_b_teste1:
  optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                   (BNot (BGt (ANum 4) (ANum 8))).
Proof.
  unfold optimize_0plus_b; try reflexivity.
Qed.

Example optimize_0plus_b_teste2:
  optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) =
                   (BAnd (BLe (ANum 4) (ANum 5)) BTrue).
Proof.
  unfold optimize_0plus_b; try reflexivity.
Qed.

Theorem optimize_0plus_b_corretude : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b.
  induction b; simpl;
  repeat rewrite optimize_0plus_corretude;
  try rewrite IHb; 
  try rewrite IHb1, IHb2;
  reflexivity.
Qed.

(* Exercício *)
(* Exercício de projeto: A otimização implementada pela nossa função optimize_0plus é 
apenas uma das muitas otimizações possíveis em expressões aritméticas e booleanas. 
Escreva um otimizador mais sofisticado e prove que ele está correto. (Você provavelmente 
achará mais fácil começar pequeno — adicione apenas uma otimização simples e sua 
respectiva prova de correção — e construa incrementalmente algo mais interessante.) *)

Fixpoint optimize_1times (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => APlus (optimize_1times e1) (optimize_1times e2)
  | AMinus e1 e2 => AMinus (optimize_1times e1) (optimize_1times e2)
  | AMult (ANum 1) e2 => optimize_1times e2
  | AMult e1 e2 => AMult (optimize_1times e1) (optimize_1times e2)
  end.
  
Example teste_1times :
optimize_1times (AMult (ANum 1) (AMult (ANum 1) (ANum 7))) = ANum 7.
Proof. reflexivity. Qed.

Theorem optimize_1times_corretude : forall a,
  aeval (optimize_1times a) = aeval a.

Proof.
  intros a.
  induction a;
  try (simpl; rewrite IHa1, IHa2; reflexivity).
  try reflexivity.
  - destruct a1 as [n | e1 e2 | e1 e2 | e1 e2];
    try (simpl in *; rewrite IHa1, IHa2; reflexivity);
    destruct n as [ | [ | n'']]; simpl; try reflexivity;
     rewrite IHa2; try rewrite add_0_r; try reflexivity.
Qed.

(*** Definindo Novas Táticas ***)

(* O Rocq também oferece recursos para ''programar'' em scripts de táticas.

 O recurso Ltac ilustrado abaixo fornece uma forma prática de definir ''táticas de atalho'' que 
agrupam várias táticas em um único comando. 

O Ltac também inclui correspondência de padrões sintáticos (pattern-matching) na meta e 
no contexto, bem como recursos gerais de programação.

Ele é útil para automação de provas e existem várias abordagens para programar com o 
Ltac. Como é um estilo de linguagem que você talvez não tenha visto antes, uma boa r
eferência é o livro-texto ''Certified Programming with Dependent Types'' (CPDT), que é 
mais avançado do que precisaremos neste curso, mas é considerado por muitos a melhor 
referência para programação em Ltac.

Apenas para referência futura: o Rocq fornece outras duas maneiras de definir novas 
táticas. Existe um comando Tactic Notation que permite definir novas táticas com 
controle personalizado sobre sua sintaxe concreta. E também há uma API de baixo nível 
que pode ser usada para construir táticas que manipulam diretamente as estruturas 
internas do Rocq. Não precisaremos de nenhuma delas para os propósitos atuais.

Aqui está um exemplo de script Ltac chamado invert. *)
Ltac invert H :=
  inversion H; subst; clear H.

(* Isso define uma nova tática chamada invert que recebe uma hipótese H como argumento e 
executa a sequência de comandos inversion H; subst; clear H. Isso nos dá uma maneira 
rápida de fazer inversão em evidências e construtores, reescrever com as equações geradas 
e remover a hipótese redundante no final. *)

Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
  intros.
  invert H.
  reflexivity.
Qed.

(*** A Tática lia ***)

(* A tática lia implementa um procedimento de decisão para aritmética linear inteira, um 
subconjunto da lógica proposicional e da aritmética. 

Se a meta for uma fórmula quantificada universalmente composta por 
  - constantes numéricas, adição (+ e S), subtração (- e pred) e multiplicação por 
    constantes (isso é o que constitui a aritmética de Presburger),
  - igualdade (= e ≠) e ordenação (≤ e >), e 
  - os conectivos lógicos ∧, ∨, ¬ e →,
então invocar lia resolverá a meta ou falhará, o que significa que a meta é efetivamente 
falsa. (Se a meta não estiver nessa forma, o lia falhará) *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

(* (Note o From Stdlib Require Import Lia. no topo deste arquivo, o que torna o lia 
disponível.) *)

(*** Algumas Táticas Úteis a Mais ***)

(* Finalmente, aqui estão algumas táticas variadas que você pode achar convenientes.

  - clear H: Remove a hipótese H do contexto.

  - subst x: Dado uma variável x, encontra uma suposição x = e ou e = x no contexto, 
    substitui x por e em todo o contexto e no objetivo atual, e remove a suposição.

  - subst: Substitui todas as suposições da forma x = e ou e = x (onde x é uma variável).

  - rename... into...: Altera o nome de uma hipótese no contexto de prova. Por exemplo,
    se o contexto inclui uma variável chamada x, então rename x into y mudará todas as 
    ocorrências de x para y.

  - assumption: Tenta encontrar uma hipótese H no contexto que corresponda exatamente ao 
    objetivo; se uma for encontrada, resolve o objetivo.

  - contradiction: Tenta encontrar uma hipótese H no contexto que seja logicamente 
    equivalente a False (Falso). Se uma for encontrada, resolve o objetivo.

  - constructor: Tenta encontrar um construtor c (de alguma definição indutiva no 
    ambiente atual) que possa ser aplicado para resolver o objetivo atual. Se um for 
    encontrado, comporta-se como apply c.

Veremos exemplos de todas elas conforme formos avançando. *)

(****************************** Avaliação como uma Relação ******************************)

(* Apresentamos aeval e beval como funções definidas por Fixpoints. Outra maneira de 
pensar sobre a avaliação — que frequentemente é mais flexível — é como uma relação entre 
expressões e seus valores. Essa perspectiva leva a definições indutivas como a seguinte...*)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module HypothesisNames.

(* Um pequeno aparte sobre notação. Também poderíamos escrever a definição de aevalR da 
seguinte forma, com nomes explícitos para as hipóteses em cada caso: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

(* Este estilo nos dá mais controle sobre os nomes que o Rocq escolhe durante provas 
envolvendo aevalR, ao custo de tornar a definição um pouco mais verbosa. *)

End HypothesisNames.

(* Será conveniente termos uma notação infixa para aevalR. Escreveremos e ==> n para 
significar que a expressão aritmética e é avaliada para o valor n. *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

(* Como vimos em nosso estudo de caso sobre expressões regulares no capítulo IndProp, o 
Rocq fornece uma maneira de usar essa notação na própria definição de aevalR.*)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)

where "e '==>' n" := (aevalR e n).

(*** Notação de Regras de Inferência ***)

(* Em discussões informais, é conveniente escrever as regras para aevalR e relações 
semelhantes na forma gráfica, mais legível, de regras de inferência, onde as premissas 
acima da linha justificam a conclusão abaixo da linha. 

Por exemplo, o construtor E_APlus... 

    | E_APlus : ∀ (e1 e2 : aexp) (n1 n2 : nat),
              aevalR e1 n1 →
              aevalR e2 n2 →
              aevalR (APlus e1 e2) (n1 + n2)
          
...pode ser escrito assim como uma regra de inferência:


                                e1 ==> n1	
                                e2 ==> n2	  
                        ----------------------- (E_APlus)     
                         APlus e1 e2 ==> n1+n2	

Formalmente, não há nada de profundo nas regras de inferência: elas são apenas 
implicações. 

Você pode ler o nome da regra à direita como o nome do construtor e ler cada uma das 
quebras de linha entre as premissas acima da linha (assim como a própria linha) como →. 

Todas as variáveis mencionadas na regra (e1, n1, etc.) são implicitamente ligadas por 
quantificadores universais no início. (Tais variáveis são frequentemente chamadas de 
metavariáveis para distingui-las das variáveis da linguagem que estamos definindo. No 
momento, nossas expressões aritméticas não incluem variáveis, mas em breve as 
adicionaremos.) 

Toda a coleção de regras é entendida como estando envolvida em uma declaração Indutiva.
Em prosa informal, isso às vezes é indicado dizendo algo como ''Seja aevalR a menor 
relação fechada sob as seguintes regras...''. Por exemplo, poderíamos definir ==> como
a menor relação fechada sob estas regras: 

                	
                ---------------- (E_ANum)      
                  ANum n ==> n	

                    e1 ==> n1	
                    e2 ==> n2	
            ------------------------ (E_APlus)  
              APlus e1 e2 ==> n1+n2	

                    e1 ==> n1	
                    e2 ==> n2	
            ------------------------ (E_AMinus)  
              AMinus e1 e2 ==> n1-n2	

                    e1 ==> n1	
                    e2 ==> n2	
            ------------------------ (E_AMult)  
              AMult e1 e2 ==> n1*n2	
*)

(* Exercício *)
(* Aqui está, novamente, a definição no Rocq da função beval:

  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       ⇒ true
    | BFalse      ⇒ false
    | BEq a1 a2   ⇒ (aeval a1) =? (aeval a2)
    | BNeq a1 a2  ⇒ negb ((aeval a1) =? (aeval a2))
    | BLe a1 a2   ⇒ (aeval a1) <=? (aeval a2)
    | BGt a1 a2   ⇒ negb ((aeval a1) <=? (aeval a2))
    | BNot b      ⇒ negb (beval b)
    | BAnd b1 b2  ⇒ andb (beval b1) (beval b2)
    end.

Escreva uma definição correspondente da avaliação booleana como uma relação (em notação 
de regra de inferência). 
            
          --------------------- (E_BTrue)
             BTrue ==>b true

          --------------------- (E_BFalse)
             BFalse ==>b false

                e1 ==> n1
                e2 ==> n2
          ---------------------------- (E_BEq)
          BEq e1 e2 ==>b (n1 =? n2)

                e1 ==> n1
                e2 ==> n2
          ---------------------------- (E_BNeq)
          BNeq e1 e2 ==>b negb (n1 =? n2)

                e1 ==> n1
                e2 ==> n2
          ---------------------------- (E_BLe)
          BLe e1 e2 ==>b (n1 <=? n2)

                e1 ==> n1
                e2 ==> n2
          ---------------------------- (E_BGt)
          BGt e1 e2 ==>b negb (n1 <=? n2)

                b ==>b bv
          ---------------------------- (E_BNot)
             BNot b ==>b negb bv

             b1 ==>b bv1
             b2 ==>b bv2
          ---------------------------- (E_BAnd)
          BAnd b1 b2 ==>b andb bv1 bv2
*)

(*** Equivalência das Definições ***)

(* É simples provar que as definições relacional e funcional da avaliação concordam: *)

Theorem aevalR_iff_aeval : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H.
    induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    + (* E_APlus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a;
       simpl; intros; subst.
    + (* ANum *)
      apply E_ANum.
    + (* APlus *)
      apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.

(* Novamente, podemos tornar a prova um pouco mais curta usando alguns táticos (tacticals). *)

Theorem aevalR_iff_aeval' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* TRABALHADO EM AULA *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* Exercício *)
(* Escreva uma relação bevalR no mesmo estilo de aevalR e prove que ela é equivalente a 
beval. *)
Reserved Notation "e '==>b' b"
                  (at level 90, left associativity).

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : bevalR (BTrue) true
  | E_BFalse : bevalR (BFalse) false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1)
    (H2 : aevalR e2 n2) : bevalR (BEq e1 e2) (n1 =? n2)
  | E_BNeq (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1)
    (H2: aevalR e2 n2) : bevalR (BNeq e1 e2) (negb (n1 =? n2))
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1)
    (H2 : aevalR e2 n2) : bevalR (BLe e1 e2) (n1 <=? n2)
  | E_BGt (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1)
    (H2 : aevalR e2 n2) : bevalR (BGt e1 e2) (negb (n1 <=? n2))
  | E_BNot (b : bexp) (bv : bool) (H : bevalR b bv) : bevalR (BNot b) (negb bv)
  | E_BAnd (b1 b2 : bexp) (bv1 bv2 : bool) (H1 : bevalR (b1) bv1) (H2 : bevalR (b2) bv2) :
    bevalR (BAnd b1 b2) (andb bv1 bv2)

where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma bevalR_iff_beval : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  split.
  - (* -> *)
    intros H; induction H; simpl; try reflexivity; 
    try (apply aevalR_iff_aeval in H1; 
    apply aevalR_iff_aeval in H2;
    rewrite H1, H2; reflexivity);
    try (rewrite IHbevalR; reflexivity);
    try (rewrite IHbevalR1, IHbevalR2; reflexivity). 
  - (* <- *)
    generalize dependent bv.
    induction b; simpl; intros; subst; constructor;
    try apply aevalR_iff_aeval; try apply IHb; 
    try apply IHb1; try apply IHb2; reflexivity.
Qed.

End AExp.

(*** Definições Computacionais vs. Relacionais ***)

(* Para as definições de avaliação de expressões aritméticas e booleanas, a escolha 
entre usar definições funcionais ou relacionais é principalmente uma questão de 
preferência: qualquer uma das duas funciona bem. 

No entanto, há muitas situações em que as definições relacionais de avaliação funcionam 
muito melhor do que as funcionais. *)

Module aevalR_division.

(* Por exemplo, suponha que quiséssemos estender as operações aritméticas com a divisão: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NOVO *)

(* Estender a definição de aeval para lidar com essa nova operação não seria direto 
(o que deveríamos retornar como o resultado de ADiv (ANum 5) (ANum 0)?). Mas estender 
aevalR é muito fácil. *)
Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) : (* <----- NOVO *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

(* Note que esta relação de avaliação corresponde a uma função parcial: Existem algumas 
entradas para as quais ela não especifica uma saída. *)

End aevalR_division.

Module aevalR_extended.

(* Ou suponha que queremos estender as operações aritméticas com um gerador de números 
não determinístico qualquer que, quando avaliado, pode produzir qualquer número. 

(Note que isso não é o mesmo que fazer uma escolha probabilística entre todos os números 
possíveis — não estamos especificando nenhuma distribuição de probabilidade específica 
para os resultados, apenas dizendo quais resultados são possíveis.) *)

Inductive aexp : Type :=
  | AAny (* <--- NOVO *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(* Novamente, estender aeval seria complicado, pois agora a avaliação não é uma função 
determinística de expressões para números; mas estender aevalR não é problema... *)
Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n (* <--- NOVO *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(* Neste ponto, você pode estar se perguntando: Qual desses estilos devo usar por padrão?

Nos exemplos que acabamos de ver, as definições relacionais acabaram se mostrando mais 
úteis do que as funcionais. Para situações como essas, onde a coisa que está sendo 
definida não é fácil de expressar como uma função, ou de fato onde ela não é uma função, não 
há escolha real. Mas e quando ambos os estilos são viáveis?

Um ponto a favor das definições relacionais é que elas podem ser mais elegantes e fáceis 
de entender.

Outro é que o Rocq gera automaticamente princípios de inversão e indução agradáveis a 
partir de definições Indutivas.

Por outro lado, as definições funcionais muitas vezes podem ser mais convenientes:
  * As funções são automaticamente determinísticas e totais; para uma definição relacional, 
    temos que provar essas propriedades explicitamente se precisarmos delas.
  * Com as funções, também podemos aproveitar o mecanismo de computação do Rocq para 
    simplificar expressões durante as demonstrações.

Além disso, as funções podem ser diretamente 'extraídas' de Gallina para código executável 
em OCaml ou Haskell.

Em última análise, a escolha muitas vezes se resume aos detalhes de uma situação 
específica ou simplesmente a uma questão de gosto. De fato, em grandes desenvolvimentos 
em Rocq, é comum ver uma definição dada em ambos os estilos, funcional e relacional, 
além de um lema afirmando que os dois coincidem, permitindo que demonstrações futuras 
alternem de um ponto de vista para o outro à vontade. *)

(******************************* Expressões Com Variáveis *****************************)

(* Vamos voltar à definição do Imp, onde a próxima coisa que precisamos fazer é 
enriquecer nossas expressões aritméticas e booleanas com variáveis. 

Para manter as coisas simples, assumiremos que todas as variáveis são globais e que elas 
contêm apenas números. *)

(*** Estados ***)
(* Como queremos consultar as variáveis para descobrir seus valores atuais, usaremos 
mapas totais do capítulo Maps. 

Um estado de máquina (ou apenas estado) representa os valores atuais de todas as 
variáveis em um determinado ponto da execução de um programa. 

Por simplicidade, assumimos que o estado está definido para todas as variáveis, embora 
qualquer programa específico consiga mencionar apenas um número finito delas. Como cada 
variável armazena um número natural, podemos representar o estado como um mapa total de 
strings (nomes de variáveis) para `nat`, e usaremos `0` como o valor padrão no 
repositório.*)

Definition estado := mapa_total nat.

(*** Sintaxe ***)

(* Podemos adicionar variáveis às expressões aritméticas que tínhamos antes simplesmente 
incluindo mais um construtor:*)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NOVO *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(* Definir alguns nomes de variáveis como abreviações notacionais tornará os exemplos 
mais fáceis de ler: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(* (Esta convenção para nomear variáveis de programas (X, Y, Z) entra um pouco em 
conflito com o nosso uso anterior de letras maiúsculas para tipos. Como não estamos 
usando polimorfismo intensamente nos capítulos desenvolvidos até o Imp, essa 
sobrecarga não deve causar confusão.)

A definição de bexps permanece inalterada (exceto pelo fato de que agora ela se refere 
às novas aexps): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(*** Notações ***)

(* Para tornar os programas Imp mais fáceis de ler e escrever, introduzimos algumas 
notações e coerções implícitas. Você não precisa entender exatamente o que essas 
declarações fazem. No entanto, resumidamente:

  - A declaração Coercion estipula que uma função (ou construtor) pode ser usada 
    implicitamente pelo sistema de tipos para coergir um valor do tipo de entrada em um 
    valor do tipo de saída. Por exemplo, a declaração de coerção para AId nos permite 
    usar strings simples quando um aexp é esperado; a string será implicitamente 
    envolvida com AId.

  - Declare Custom Entry com instrui o Rocq a criar uma nova ''gramática personalizada'' 
    para fazer o parsing (análise sintática) de expressões e programas Imp. A primeira 
    declaração de notação após isso diz ao Rocq que qualquer coisa entre <{ e }> deve 
    ser analisada usando a gramática do Imp. Novamente, não é necessário entender os 
    detalhes, mas é importante reconhecer que estamos definindo novas interpretações 
    para alguns operadores familiares como +, -, ×, =, ≤, etc., quando eles ocorrem 
    entre <{ e }>. *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (e custom com, format "'[hv' <{ '/ ' '[v' e ']' '/' }> ']'") : com_scope.
Notation "( x )" := x (in custom com, x at level 99).
Notation "x" := x (in custom com at level 0, x constr at level 0).
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 1,
                      y constr at level 1).
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

(* Agora podemos escrever 3 + (X × 2) em vez de APlus 3 (AMult X 2), e true && ~(X ≤ 4) 
em vez de BAnd true (BNot (BLe X 4)). *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

(*** Avaliação ***)

(* Os avaliadores aritméticos e booleanos agora precisam ser estendidos para lidar com 
variáveis da maneira óbvia, recebendo um estado st como um argumento extra:*)

Fixpoint aeval (st : estado) (* <--- NOVO *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NOVO *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : estado) (* <--- NOVO *)
               (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

(* Podemos usar nossa notação para mapas totais no caso específico de estados -- ou 
seja, escrevemos o estado vazio como (__ !-> 0). *)

Definition empty_st := (__ !-> 0).

(* Além disso, podemos adicionar uma notação para um 'estado unitário' (ou 'estado de 
elemento único') com apenas uma variável associada a um valor. *)

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100, right associativity).

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

(*************************************** Comandos *************************************)

(* Agora estamos prontos para definir a sintaxe e o comportamento dos comandos (ou 
declarações) do Imp. *)

(**** Sintaxe ***)

(* Informalmente, os comandos $c$ são descritos pela seguinte gramática BNF.
     c := skip
        | x := a
        | c ; c
        | if b then c else c end
        | while b do c end

Aqui está a definição formal da sintaxe abstrata dos comandos: *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(* Assim como fizemos para as expressões, podemos usar algumas declarações de Notação 
para tornar a leitura e a escrita de programas Imp mais convenientes. *)

Notation "'skip'" := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y" := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x := y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if' x 'then' '/ ' y '/' 'else' '/ ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while' x 'do' '/ ' y '/' 'end' ']'") : com_scope.

(* Por exemplo, aqui está a função fatorial novamente, escrita como uma definição formal 
do Rocq. Quando este comando terminar, a variável Y conterá o fatorial do valor inicial 
de X. *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

(*** Eliminação de Notações (Desugaring Notations) ***)

(* O Rocq oferece um conjunto rico de recursos para gerenciar a crescente complexidade 
dos objetos com os quais trabalhamos, tais como coerções e notações. No entanto, o uso 
intenso deles pode dificultar a compreensão do que as expressões que digitamos realmente 
significam. Nessas situações, muitas vezes é instrutivo ''desativar'' esses recursos 
para obter uma visão mais elementar das coisas, utilizando os seguintes comandos:

  - Unset Printing Notations (desfaz com Set Printing Notations)
  - Set Printing Coercions (desfaz com Unset Printing Coercions)
  - Set Printing All (desfaz com Unset Printing All)

Esses comandos também podem ser usados no meio de uma prova para detalhar o objetivo 
(goal) e o contexto atuais. *)

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAsgn Z X)
        (CSeq (CAsgn Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAsgn Y (AMult Y Z))
                            (CAsgn Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

Set Printing Coercions.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

Print fact_in_coq.
(* ===>
  fact_in_coq =
  <{ Z := (AId X);
     Y := (ANum 1);
     while ~ (AId Z) = (ANum 0) do
       Y := (AId Y) * (AId Z);
       Z := (AId Z) - (ANum 1)
     end }>
       : com *)
Unset Printing Coercions.

(*** Localizar Novamente ***)

(** Encontrando identificadores **)

(* Quando usado com um identificador, o comando Locate imprime o caminho completo de 
cada valor no escopo com o mesmo nome. Isso é útil para solucionar problemas causados 
pelo sombreamento de variáveis (variable shadowing). *)

Locate aexp.
(* ===>
      Inductive
LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.aexp
Inductive
LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.AExp.aexp
(shorter name to refer to it in current context is AExp.aexp)
Inductive
LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.aevalR_division.aexp
(shorter name to refer to it in current context is aevalR_division.aexp)
Inductive
LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.aevalR_extended.aexp
(shorter name to refer to it in current context is aevalR_extended.aexp) *)

(** Encontrando notações **)

(* Ao se depatrar com uma notação desconhecida, você pode usar o Locate com uma string 
contendo um de seus símbolos para ver suas interpretações possíveis. *)

Locate "&&".
(* ===>
    Notation
      "x && y" := BAnd x y (default interpretation)
      "x && y" := andb x y : bool_scope (default interpretation)
*)
Locate ";".
(* ===>
    Notation
      "x '⊢>' v ';' m" := (update m x v) (default interpretation)
      "x ; y" := (CSeq x y) (default interpretation)
      "x '!->' v ';' m" := (t_update m x v) (default interpretation)
      " x ; y ; .. ; z " := cons x (cons y .. (cons z nil) ..) : list_scope
      (default interpretation) *)
Locate "while".
(* ===>
    Notation
      "'while' x 'do' y 'end'" :=
          (CWhile x y) (default interpretation)
*)

(*** Mais Exemplos ***)

(** Atribuição: **)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

(** Laços (Loops) **)

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

(** Um loop infinito: **)

Definition loop : com :=
  <{ while true do
       skip
     end }>.

(********************************** Avaliando Comandos ********************************)

(* Em seguida, precisamos definir o que significa avaliar um comando Imp. O fato de 
que os loops while não terminam necessariamente torna a definição de uma função de 
avaliação complicada... *)

(*** Avaliação como uma Função (Tentativa Fracassada) ***)

(* Aqui está uma tentativa de definir uma função de avaliação para comandos (com um caso 
de while falso).*)

Fixpoint ceval_fun_no_while (st : estado) (c : com) : estado :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> aeval st a ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st (* falso *)
  end.