(* Auto *)

(* Mais Automação *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith List.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
Require Import LFPTBR.h_Mapas_Totais_e_Parciais.a_Mapas_Totais_e_Parciais.
Require Import LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.
Set Default Goal Selector "!".

(* Até agora, usamos a parte manual das facilidades de táticas do Rocq. Neste capítulo, 
aprenderemos mais sobre alguns dos poderosos recursos de automação do Rocq: busca de provas por 
meio da tática auto, raciocínio direto (forward reasoning) automatizado por meio do mecanismo 
de correspondência de hipóteses do Ltac, e instanciação adiada de variáveis existenciais usando 
eapply e eauto. Usar esses recursos junto com as facilidades de scripting do Ltac nos permitirá 
tornar algumas de nossas provas surpreendentemente curtas! Usadas adequadamente, elas também 
podem tornar as provas mais fáceis de manter e mais resistentes a mudanças nas definições 
subjacentes. Um tratamento mais aprofundado de auto e eauto pode ser encontrado no capítulo 
UseAuto em Programming Language Foundations.

Há outra grande categoria de automação que ainda não discutimos muito, a saber, procedimentos 
de decisão integrados para tipos específicos de problemas: lia é um exemplo, e no final do 
capítulo introduziremos mais um chamado congruence.

Começamos, porém, com a tática auto, e nosso exemplo motivador será a prova a seguir, repetida 
com apenas algumas pequenas mudanças em relação ao capítulo Imp. Vamos simplificar essa prova 
em várias etapas.*)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
- (* E_Skip *) reflexivity.
- (* E_Asgn *) reflexivity.
- (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
- (* b é avaliado como verdadeiro *)
    apply IHE1. assumption.
- (* b é avaliado como falso (contradição) *)
    rewrite H in H5. discriminate.
  (* E_IfFalse *)
- (* b é avaliado como verdadeiro (contradição) *)
    rewrite H in H5. discriminate.
- (* b é avaliado como falso *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
- (* b é avaliado como falso *)
    reflexivity.
- (* b é avaliado como verdadeiro (contradição) *)
    rewrite H in H2. discriminate.
  (* E_WhileTrue *)
- (* b é avaliado como falso (contradição) *)
    rewrite H in H4. discriminate.
- (* b é avaliado como verdadeiro *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption. Qed.

(**************************************** A Tática auto ***************************************)

(* Até agora, nossos scripts de prova trabalham majoritariamente de trás para frente (backward), 
aplicando hipóteses ou lemas relevantes ao objetivo pelo nome, um de cada vez. *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR. apply HPQ. assumption.
Qed.

(* A tática auto tenta nos livrar desse trabalho repetitivo procurando uma sequência de 
aplicações ao objetivo que, por fim, o provará: *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(* A tática auto resolve metas (goals) que podem ser resolvidas por qualquer combinação de 
intros e apply.

Usar auto é sempre ''seguro'' no sentido de que ela nunca vai falhar e nunca vai alterar o 
estado da prova: ou ela resolve completamente a meta atual, ou não faz nada.

Aqui está um exemplo maior mostrando o poder do auto: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(* Intuitivamente, podemos entender a tática auto como a execução recursiva dos seguintes 
passos de busca regressiva (backward search):

  - Se assumption fechar a meta (goal), terminamos.
  
  - Se a meta for uma implicação (→) ou um quantificador universal (∀), chama a tática intro 
    (a versão unária de intros) e continua com a nova meta.
    
  - Caso contrário, aplica uma hipótese cuja conclusão se unifique com a meta e faz recursão 
    nas novas submetas. Se alguma submeta não puder ser fechada, retrocede (backtrack) e tenta 
    qualquer outra hipótese que se unifique com a meta.
    
Se nenhum caminho candidato levar a uma prova completa, auto não faz nada, deixando a meta 
inalterada.

Se auto não resolver nossa meta como esperado, podemos usar debug auto para ver um rastro 
(trace) da execução. Na verdade, debug auto imprime todo o rastro de busca mesmo quando auto 
tem sucesso, então também podemos usá-lo para observar o auto fazendo backtrack: *)

Example auto_algorithm : forall (P Q R: Prop),
  (Q -> R) -> (* HQR : requer Q -- beco sem saída *)
  ((P -> P) -> R) -> (* HPPR : requer P → P -- provado por intro
                                                    e assumption *)
  R.
Proof. intros P Q R HQR HPPR. debug auto. Qed.

(* A busca de prova (proof search) poderia, em princípio, levar um tempo arbitrariamente longo, 
portanto há um limite para quão fundo o auto vai procurar (por padrão, 5). *)

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  intros P Q R S T U HPQ HQR HRS HST HTU HP.
  (* o auto não faz nada para esta meta, mesmo que ela pareça solucionável *)
  auto.
  (* Vamos ver o que o auto faz com a profundidade de busca padrão
     de 5 adicionando a palavra-chave debug: *)
  debug auto.
  (* O que ele fez foi o seguinte: *)
  (* apply HTU. *)
  (* apply HST. *)
  (* apply HRS. *)
  (* apply HQR. *)
  (* apply HPQ. *)
  (* Mas depois ele não conseguiu provar P,
     mesmo tendo P como hipótese *)
  (* Com um argumento opcional para o auto, podemos alterar a profundidade
     máxima de busca; neste caso, uma profundidade de 6 resolve o problema: *)
  auto 6.
Qed.

(* Ao procurar potenciais provas para a meta atual (goal), o auto considera as hipóteses no 
contexto atual juntamente com uma base de dicas (hint database) contendo outros lemas e 
construtores. Alguns lemas comuns sobre igualdade e operadores lógicos já vêm instalados nessa 
base de dicas por padrão. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(* Se quisermos ver quais fatos o auto está usando, podemos utilizar info_auto em vez disso. Ao 
contrário de debug auto, que também imprime os caminhos que falharam, info_auto exibe apenas o 
caminho de prova bem-sucedido. *)

Example auto_example_4' : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  info_auto.
Qed.

(* O auto usou os seguintes fatos da base de dicas (hint database) padrão: *)

Check or_intror : forall A B : Prop, B -> A \/ B.
Check conj : forall A B : Prop, A -> B -> A /\ B.

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.

(* O auto engloba o reflexivity porque eq_refl é um fato na base de dicas 
(hint database) padrão: *)

Check @eq_refl : forall A (x:A), x = x.

(* Podemos estender a base de dicas (hint database) apenas para o propósito de uma única 
aplicação de auto escrevendo auto using .... *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

(* Certamente, em qualquer desenvolvimento haverá provavelmente alguns construtores e lemas 
específicos que são usados com muita frequência nas provas. Podemos adicioná-los à base de 
dicas (hint database) global escrevendo 

  Hint Resolve T : core. 
  
no nível superior (top level), onde T é um teorema de nível superior ou um construtor de uma 
proposição definida indutivamente (isto é, qualquer coisa cujo tipo seja uma implicação). Como 
um atalho, podemos escrever 

  Hint Constructors c : core. 
  
para instruir o Rocq a fazer um Hint Resolve para todos os construtores da definição indutiva 
de c. 

Às vezes também é necessário adicionar 

  Hint Unfold d : core. 
  
onde d é um símbolo definido, para que o auto saiba desdobrar (unfold) os usos de d, 
possibilitando assim mais opções para aplicar os lemas que ele conhece.

Também é possível definir bases de dicas especializadas (além de core) que podem ser ativadas 
apenas quando necessário; de fato, é uma boa prática criar suas próprias bases de dicas em vez 
de poluir a core.

Consulte o manual de referência do Rocq para mais detalhes. *)

Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto. (* pega uma dica da base de dados (hint database) *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* não faz nada *)
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* tente também: info_auto. *)
Qed.

(* Note que o comando Hint Unfold is_fortytwo acima do exemplo é necessário porque, ao contrário 
da tática apply normal, os passos simples de apply executados pelo auto não fazem nenhum 
desdobramento automático (unfolding).

Vamos fazer uma primeira passada em ceval_deterministic, usando auto para simplificar o script 
de prova. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
    inversion E2; subst; (* <- termina com ; *)
    auto. (* <---- aqui é um bom lugar para tentar o auto *)
- (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto. (* <---- aqui é outro *)
- (* E_IfTrue *)
    rewrite H in H5. discriminate.
- (* E_IfFalse *)
    rewrite H in H5. discriminate.
- (* E_WhileFalse *)
    rewrite H in H2. discriminate.
- (* E_WhileTrue, com b falso *)
    rewrite H in H4. discriminate.
- (* E_WhileTrue, com b verdadeiro *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. (* <---- e outro *)
Qed.

(* Quando estamos usando uma determinada tática muitas vezes em uma prova, podemos usar uma 
variante do comando Proof para tornar essa tática padrão dentro da prova. Escrever Proof with t 
(onde t é uma tática arbitrária) nos permite usar t1... como uma abreviação para t1;t dentro da 
prova. Como ilustração, aqui está uma versão alternativa da prova anterior, usando Proof with 
auto. *)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
    inversion E2; subst...
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *...
  - (* E_IfTrue *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, com b falso *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, com b verdadeiro *)
    rewrite (IHE1_1 st'0 H3) in *...
Qed.

(*** Exercícios ***)


Require Import LFPTBR.g_IndProp.a_IndProp.
Module Exercises. 
Import Bombeamento.

(* Exercício *)
(* Use auto, lia e ; para provar novamente este lema em uma ''única'' linha. A prova ''oficial'' 
em IndProp leva cerca de uma dúzia de linhas. *)
Local Notation "x <= y" := (Peano.le x y) (at level 70, no associativity).
Local Notation "x >= y" := (Peano.ge x y) (at level 70, no associativity).

Lemma constante_de_bombeamento_maior_igual_1 :
  forall T (er : exp_reg T),
  constante_de_bombeamento er >= 1.
Proof.
  induction er; simpl; lia.
Qed.

(** Exercício de otimização de expressões regulares **)

(* Exercício *)
(* Como uma ilustração simples dos benefícios da automação, vamos considerar outro problema 
sobre expressões regulares, que formalizamos em IndProp. Um determinado conjunto de cadeias 
(strings) pode ser denotado por muitas expressões regulares diferentes. Por exemplo, 
Concatenar CadeiaVazia re casa (matches) exatamente as mesmas cadeias que re. Podemos escrever uma 
função que ''otimiza'' qualquer expressão regular em uma potencialmente mais simples aplicando 
esse fato em toda a expressão regular (r.e.). (Note que, por simplicidade, a função não otimiza 
expressões que surgem como resultado de outras otimizações.) *)

Fixpoint re_opt {T:Type} (re: exp_reg T) : exp_reg T :=
  match re with
  | Concatenar _ ConjuntoVazio => ConjuntoVazio
  | Concatenar CadeiaVazia re2 => re_opt re2
  | Concatenar re1 CadeiaVazia => re_opt re1
  | Concatenar re1 re2 => Concatenar (re_opt re1) (re_opt re2)
  | Uniao ConjuntoVazio re2 => re_opt re2
  | Uniao re1 ConjuntoVazio => re_opt re1
  | Uniao re1 re2 => Uniao (re_opt re1) (re_opt re2)
  | Estrela ConjuntoVazio => CadeiaVazia
  | Estrela CadeiaVazia => CadeiaVazia
  | Estrela re => Estrela (re_opt re)
  | ConjuntoVazio => ConjuntoVazio
  | CadeiaVazia => CadeiaVazia
  | Char x => Char x
  end.

(* Gostaríamos de mostrar a equivalência das expressões regulares (re's) com sua forma 
''otimizada''. Aqui está uma prova manual incrivelmente tediosa de (uma direção de) sua correção: *)

Lemma re_opt_match : forall T (re: exp_reg T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
       | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MVazio *) simpl. apply MVazio.
  - (* MChar *) simpl. apply MChar.
  - (* MConcatenar *) simpl.
    destruct re1.
    + inversion IH1.
    + inversion IH1. simpl. destruct re2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
      * apply MConcatenar.
        -- apply IH1.
        -- apply IH2.
  - (* MUniaoEsquerda *) simpl.
    destruct re1.
    + inversion IH.
    + destruct re2.
      * apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
      * apply MUniaoEsquerda. apply IH.
  - (* MUniaoDireita *) simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
      * apply MUniaoDireita. apply IH.
 - (* MEstrela0 *) simpl.
    destruct re.
    + apply MVazio.
    + apply MVazio.
    + apply MEstrela0.
    + apply MEstrela0.
    + apply MEstrela0.
    + simpl.
      destruct re.
      * apply MEstrela0.
      * apply MEstrela0.
      * apply MEstrela0.
      * apply MEstrela0.
      * apply MEstrela0.
      * apply MEstrela0.
 - (* MEstrelaConcatenar *) simpl.
   destruct re.
   + inversion IH1.
   + inversion IH1. inversion IH2. apply MVazio.
   + apply estrela_concatenar.
     * apply MEstrela1. apply IH1.
     * apply IH2.
   + apply estrela_concatenar.
     * apply MEstrela1. apply IH1.
     * apply IH2.
   + apply estrela_concatenar.
     * apply MEstrela1. apply IH1.
     * apply IH2.
   + apply estrela_concatenar.
     * apply MEstrela1. apply IH1.
     * apply IH2.
Qed.

(* Use auto para encurtar a prova. A prova acima tem cerca de 200 linhas. Reduza-a para 50 linhas 
ou menos com densidade semelhante. Elimine todos os usos de apply, removendo assim a necessidade 
de nomear construtores e lemas específicos sobre expressões regulares.

Dica: Você pode usar uma abordagem de baixo para cima (bottom-up). Primeiro, copie e cole a 
prova inteira abaixo. Em seguida, automatize os marcadores (bullets) mais internos primeiro, 
avançando para os mais externos. Verifique com frequência se a prova inteira ainda compila. Se 
não compilar, desfaça as alterações mais recentes que você fez até voltar a uma prova que 
compila. *)

Hint Constructors exp_match : core. 

Lemma re_opt_match' : forall T (re: exp_reg T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
       | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    simpl.
  - (* MVazio *) constructor.
  - (* MChar *) constructor.
  - (* MConcatenar *)
    destruct re1; destruct re2; simpl in *;
      try (inversion IH1; fail);                              
      try (inversion IH2; fail);                             
      try (inversion IH1; simpl; auto; fail);                
      try (inversion IH2; rewrite app_nil_r; auto; fail);     
      auto.                                                   
  - (* MUniaoEsquerda *)
    destruct re1; destruct re2; simpl in *;
      try (inversion IH; fail); auto.
  - (* MUniaoDireita *)
    destruct re1; destruct re2; simpl in *;
      try (inversion IH; fail); auto.
  - (* MEstrela0 *)
    destruct re; simpl in *; auto.
  - (* MEstrelaConcatenar *)
    destruct re; simpl in *;
      try (inversion IH1; fail);
      try (inversion IH1; inversion IH2; constructor; fail);
      auto.
Qed.

(** Exercício Opcional do Lema do Bombeamento **)

(* Exercício *)
(* Use auto, lia, repeat, ;, try, etc. para encurtar a demonstração oficial do exercício 
opcional mais forte do Lema do Bombeamento de IndProp. *)
From Stdlib Require Import List. (* ou From Coq Require Import Lists.List. *)
Import ListNotations.
Open Scope list_scope.

Lemma bombeamento : forall T (er : exp_reg T) c,
  c =~ er ->
  constante_de_bombeamento er <= length c ->
  exists c1 c2 c3,
    c = c1 ++ c2 ++ c3 /\
    c2 <> @nil T /\
    length c1 + length c2 <= constante_de_bombeamento er /\
    forall m, c1 ++ nconc m c2 ++ c3 =~ er.
Proof.
  intros T er c Hmatch.
  induction Hmatch
    as [ | x | c1 er1 c2 er2 Hmatch1 IH1 Hmatch2 IH2
       | c1 er1 er2 Hmatch IH | c2 er1 er2 Hmatch IH
       | er | c1 c2 er Hmatch1 IH1 Hmatch2 IH2 ]; simpl.
  - (* MVazio *) lia.
  - (* MChar *) lia.
  - (* MConcatenar *)
    destruct (Nat.lt_ge_cases (constante_de_bombeamento er1) (length c1))
      as [Hlt | Hge].
    + (* c1 sozinho já passa da constante de er1 *)
      intros Hsum.
      assert (Hle : constante_de_bombeamento er1 <= length c1) by lia.
      apply IH1 in Hle.
      destruct Hle as [sa1 [sa2 [sa3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
      exists sa1, sa2, (sa3 ++ c2). split; try rewrite H_eq; try split; try split; 
      try lia; try intros m; repeat (rewrite app_assoc);
      try constructor; try rewrite <- app_assoc; auto.
    + (* c2 sozinho já alcança a constante de er2 *)
      intros Hsum.
      rewrite length_app in Hsum.
      assert (Hc2 : constante_de_bombeamento er2 <= length c2) by lia.
      destruct (IH2 Hc2) as [s1 [s2 [s3 [Heq [Hne [Hlen Hall]]]]]].
      (* c1 inteiro fica na frente do bloco bombeável, que vem de c2 *)
      exists (c1 ++ s1), s2, s3.
      repeat split; try rewrite Heq; try rewrite length_app;
      repeat rewrite app_assoc; try discriminate; try lia; auto.
      intros m. rewrite <- app_assoc. constructor; auto.
  - (* MUniaoEsquerda *)
    intros Hsum.
    assert (Hle1 : constante_de_bombeamento er1 <= length c1) by lia.
    apply IH in Hle1.
    destruct Hle1 as [sc1 [sc2 [sc3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
    exists sc1, sc2, sc3.
    split; try split; try constructor; try lia; auto.
  - (* MUniaoDireita *)
    intros Hsum.
    assert (Hle2 : constante_de_bombeamento er2 <= length c2) by lia.
    apply IH in Hle2.
    destruct Hle2 as [sc1 [sc2 [sc3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
    exists sc1, sc2, sc3.
    split; try split; try split; try lia; auto.
  - (* MEstrela0 *)
    pose proof (constante_de_bombeamento_maior_igual_1 T er).
    lia.
  - (* MEstrelaConcatenar *)
    intros Hsum.
    destruct (Nat.lt_ge_cases (constante_de_bombeamento er) (length c1))
      as [Hlt | Hge].
    + assert (Hle : constante_de_bombeamento er <= length c1) by lia.
      apply IH1 in Hle.
      destruct Hle as [sa1 [sa2 [sa3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
      exists sa1, sa2, (sa3 ++ c2). split; try rewrite H_eq;
 try split;
        try split; try intros m; repeat (rewrite app_assoc);
        try constructor; try rewrite <- app_assoc; auto.
    + (* repetir c1 e depois c2 continua casando com Estrela er *)
      assert (Hbomb : forall m, nconc m c1 ++ c2 =~ Estrela er).
      { induction m as [ | m' IHm]; 
        simpl; try rewrite <- app_assoc; auto. }
      destruct c1 as [ | h c1'].
      * (* c1 = [] : tudo vem de c2, a IH2 resolve *)
        destruct (IH2 Hsum) as [s1 [s2 [s3 [Heq [Hne [Hlen Hall]]]]]].
        exists s1, s2, s3; split; simpl; auto.

      * (* c1 não-vazio e curto : o próprio c1 é o bloco bombeável *)
        exists [], (h :: c1'), c2; split; try reflexivity; 
        try split; simpl in *; try discriminate;auto.
Qed.

End Exercises.

(************************************* Buscando Hipóteses  **************************************)

(* A prova ficou mais simples, mas ainda há um grau incômodo de repetição. Vamos começar atacando 
os casos de contradição. Cada um deles ocorre em uma situação em que temos ambas as hipóteses

    H1: beval st b = false
e
   H2: beval st b = true.

A contradição é evidente, mas demonstrá-la é um pouco complicado: precisamos localizar as duas 
hipóteses H1 e H2 e fazer um rewrite seguido de um discriminate. Queremos automatizar esse 
processo.

(Na verdade, o Rocq tem uma tática embutida congruence que faz esse trabalho nesse caso. Vamos 
ignorar essa tática por enquanto, a fim de demonstrar como construir táticas de busca para frente 
(forward-search) manualmente.)

Como primeiro passo, podemos abstrair o trecho de script em questão escrevendo uma pequena função 
em Ltac. *)

Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_IfTrue *)
    rwd H H5. (* <----- *)
  - (* E_IfFalse *)
    rwd H H5. (* <----- *)
  - (* E_WhileFalse *)
    rwd H H2. (* <----- *)
  - (* E_WhileTrue - b false *)
    rwd H H4. (* <----- *)
  - (* EWhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(* Isso já é um pouco melhor, mas nós realmente queremos que o Rocq descubra as hipóteses 
relevantes para nós. Podemos fazer isso usando o recurso match goal do Ltac. *)

Ltac find_rwd :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _
       =>
    rwd H1 H2
  end.

(* Este match goal procura duas hipóteses distintas que tenham a forma de igualdades, com a mesma 
expressão arbitrária E à esquerda e com valores booleanos conflitantes à direita. Se essas 
hipóteses forem encontradas, ele associa H1 e H2 aos seus nomes e aplica a tática rwd a H1 e H2.

Adicionar essa tática às que invocamos em cada caso da indução resolve todos os casos 
contraditórios. *)

Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
       try find_rwd; (* <------ *)
       auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_WhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(* Vamos ver os casos restantes. Cada um deles envolve reescrever uma hipótese depois de 
alimentá-la com a condição necessária. Podemos automatizar a tarefa de encontrar as hipóteses 
relevantes com as quais reescrever. *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _
    => rewrite (H1 X H2) in *
  end.

(* O padrão ∀ x, ?P x → ?L = ?R casa com qualquer hipótese da forma ''para todo x, alguma 
propriedade de x implica alguma igualdade''. A propriedade de x é associada à variável de padrão P, 
e os lados esquerdo e direito da igualdade são associados a L e R. O nome dessa hipótese é 
associado a H1. Em seguida, o padrão ?P ?X casa com qualquer hipótese que forneça evidência de que 
P vale para algum X concreto. Se ambos os padrões tiverem sucesso, aplicamos a tática rewrite 
(instanciando o x quantificado com X e fornecendo H2 como a evidência necessária para P X) em 
todas as hipóteses e no objetivo. *)

Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
    try find_rwd;
    try find_eqn; (* <------- *)
    auto.
Qed.

(* A grande recompensa dessa abordagem é que o novo script de prova é mais robusto diante de 
mudanças na nossa linguagem. Para testar isso, vamos tentar adicionar um comando REPEAT à 
linguagem. *)

Module Repeat.

Local Notation string := String.string.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

(* REPEAT se comporta como o while, exceto que a condição do laço é verificada após cada execução 
do corpo, com o laço se repetindo enquanto a condição permanecer falsa. Por causa disso, o corpo 
sempre será executado pelo menos uma vez. *)

Notation "'repeat' x 'until' y 'end'" :=
         (CRepeat x y)
            (in custom com at level 0,
             x at level 99, y at level 99).
Notation "'skip'" :=
         CSkip (in custom com at level 0).
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).
Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> estado -> estado -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st =[ c ]=> st' ->
      beval st' b = true ->
      st =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st =[ repeat c until b end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(* Nossa primeira tentativa na prova de determinismo não funciona totalmente: os casos E_RepeatEnd 
e E_RepeatLoop não são tratados pela nossa automação anterior. *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_rwd; try find_eqn; auto.
- (* E_RepeatEnd *)
    + (* b é avaliado como falso (contradição) *)
       find_rwd.
       (* opa: por que o find_rwd não resolveu isso para nós já?
          resposta: fizemos as coisas na ordem errada. *)
- (* E_RepeatLoop *)
     + (* b é avaliado como verdadeiro (contradição) *)
        find_rwd.
Qed.

(* Felizmente, para corrigir isso, basta trocar a ordem das chamadas de find_eqn e find_rwd. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_eqn; try find_rwd; auto.
Qed.

End Repeat.

(* Esses exemplos dão apenas uma amostra do que a ''hiperautomação'' pode alcançar no Rocq. Os 
detalhes de match goal são um pouco complicados (e depurar scripts que o utilizam, francamente, 
não é muito agradável). Mas vale muito a pena adicionar pelo menos usos simples às suas provas, 
tanto para evitar o tédio quanto para torná-las ''à prova de futuro''. *)

(*********************************** As táticas eapply e eauto **********************************)

(* Para encerrar o capítulo, vamos ver mais um recurso de conveniência do Rocq: sua capacidade de 
adiar a instanciação de quantificadores. Para motivar esse recurso, relembre este exemplo do 
capítulo Imp: *)

Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* Fornecemos o estado intermediário st'... *)
  apply E_Seq with (st' := X !-> 2).
- apply E_Asgn. reflexivity.
- apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* No primeiro passo da prova, tivemos que fornecer explicitamente uma expressão um tanto longa 
para ajudar o Rocq a instanciar um argumento ''oculto'' do construtor E_Seq. Isso foi necessário 
porque a definição de E_Seq... 

          E_Seq : ∀ c1 c2 st st' st'',
            st  =[ c1 ]=> st'  →
            st' =[ c2 ]=> st'' →
            st  =[ c1 ; c2 ]=> st''
            
é quantificada sobre uma variável, st', que não aparece em sua conclusão, de modo que unificar sua 
conclusão com o estado do objetivo não ajuda o Rocq a encontrar um valor adequado para essa 
variável. Se omitirmos o with, esse passo falha (''Error: Unable to find an instance for the 
variable st' '').

O que torna esse erro bobo é que o valor apropriado para st' na verdade se tornará óbvio logo no 
passo seguinte, quando aplicarmos E_Asgn. Se o Rocq pudesse simplesmente esperar até chegarmos a 
esse passo, não haveria necessidade de informarmos o valor explicitamente. É exatamente isso que 
a tática eapply permite: *)

Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* 1 *) eapply E_Seq. (* introduz a variável existencial ?st' *)
- (* 2 *) apply E_Asgn. (* instancia ?st' com X !-> ?n;
                       usando uma nova variável existencial ?n *)
    (* 3 *) simpl. reflexivity. (* instancia ?n com 2 *)
- (* 4 *) apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* A tática eapply H comporta-se exatamente como apply H, exceto pelo fato de que, após terminar 
de unificar o estado do objetivo com a conclusão de H, ela ignora a verificação de que todas as 
variáveis introduzidas no processo receberam valores concretos durante a unificação.

Se você avançar passo a passo na prova acima, verá que o estado do objetivo na posição 1 menciona 
a variável existencial ?st' em ambos os subobjetivos gerados. O próximo passo (que nos leva à 
posição 2) substitui ?st' por um valor concreto. Esse novo valor contém uma nova variável 
existencial ?n, que é instanciada, por sua vez, pelo passo seguinte com reflexivity, na posição 3. 
Quando começamos a trabalhar no segundo subobjetivo (posição 4), observamos que a ocorrência de 
?st' nesse subobjetivo foi substituída pelo valor que recebeu durante o primeiro subobjetivo.

Várias das táticas que vimos até agora, incluindo ∃, constructor e auto, possuem variantes 
semelhantes a eapply.

Por exemplo, além de ∃, o Rocq também fornece uma tática eexists. Para provar um objetivo da 
forma ∃ x, P x, a tática ∃ t exige que forneçamos um termo concreto t, alterando o objetivo para 
P t. Em vez disso, a tática eexists introduz uma nova variável existencial ?x em seu lugar, 
deixando-nos com o objetivo P ?x. O valor de ?x terá de ser determinado por unificação em algum 
passo posterior da prova. *)

Example eexists_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof.
  eexists. eapply E_IfFalse.
  - reflexivity.
  - eapply E_Asgn. reflexivity.
Qed.

(* Da mesma forma, econstructor está para constructor assim como eapply está para apply. Na 
prova de ceval'_example1, poderíamos ter escrito econstructor no lugar de eapply E_Seq: o Rocq 
escolheria o construtor correspondente (E_Seq) e deixaria o estado intermediário como uma variável 
existencial, a ser determinada em um passo posterior. Eis a prova novamente, usando econstructor. *)

Example econstructor_example :
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  econstructor.
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* A tática eauto funciona como auto, exceto pelo fato de usar eapply em vez de apply. Antes de 
usá-la em um exemplo, fornecemos algumas dicas (hints) ao eauto sobre o uso dos construtores de 
ceval e das definições de estado e mapa_total como parte de sua busca de prova. *)

Hint Constructors ceval : core.
(* HIDE CH: Acho que seria melhor escolher outro exemplo que
   não precise de `Hint Transparent` *)
Hint Transparent estado mapa_total : core.
Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof. info_eauto. Qed.

(* info_eauto nos mostra quais fatos o eauto utiliza.

Dica profissional: pode-se pensar que, como eapply e eauto são mais poderosos do que apply e auto, 
deveríamos simplesmente usá-los o tempo todo. Infelizmente, eles também são significativamente 
mais lentos, especialmente o eauto. Especialistas em Rocq tendem a usar apply e auto na maior 
parte do tempo, recorrendo às variantes com e apenas quando as variantes comuns não dão conta do 
recado. *)

(*************************** Restrições sobre Variáveis Existenciais ****************************)

(* Para que o Qed tenha sucesso, todas as variáveis existenciais precisam ser determinadas até o 
final da prova. Caso contrário, o Rocq (com razão) se recusará a aceitar a prova. Lembre-se de 
que as táticas do Rocq constroem objetos de prova (proof objects), e objetos de prova que contêm 
variáveis existenciais não estão completos. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.  Unshelve. exact 0.

(* O Rocq emite um aviso após apply HP: ''All the remaining goals are on the shelf'' (''Todos os 
objetivos restantes estão na prateleira''), o que significa que concluímos todas as nossas 
obrigações de prova de nível superior, mas, ao longo do caminho, deixamos algumas de lado para 
serem resolvidas mais tarde, e ainda não as terminamos. Tentar encerrar a prova com Qed geraria 
um erro. (Experimente!) *)

Abort.

(* Uma restrição adicional é que variáveis existenciais não podem ser instanciadas com termos que 
contenham variáveis comuns que ainda não existiam no momento em que a variável existencial foi 
criada. (A razão para essa restrição técnica é que permitir tal instanciação levaria à 
inconsistência da lógica do Rocq.)*)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
  Fail apply HP'.

(* O erro que obtemos, com alguns detalhes omitidos, é:

    cannot instantiate "?y" because "y" is not in its scope 
    (''não é possível instanciar ?y porque y não está em seu escopo'')

Neste caso, há uma correção simples: executar destruct HP antes de executar eapply HQ. *)

Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(* O apply HP' no último passo unifica a variável existencial no objetivo com a variável y.

Note que a tática assumption não funciona neste caso, uma vez que não consegue tratar variáveis 
existenciais. Entretanto, o Rocq também disponibiliza a tática eassumption, que resolve o 
objetivo se uma das premissas corresponder ao objetivo mediante a instanciação de variáveis 
existenciais. Podemos utilizá-la no lugar de apply HP', se desejarmos. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(* A tática eauto utilizará eapply e eassumption, simplificando ainda mais a prova. *)

Lemma silly2_eauto : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eauto.
Qed.

(************************ Solucionador de Igualdades: A Tática congruence ************************)

(* O Rocq possui diversas táticas de propósito específico que conseguem resolver certos tipos de 
objetivos automaticamente, com base em algoritmos para domínios matemáticos ou lógicos específicos. 
Uma dessas táticas, lia, já foi apresentada em Imp, e aqui aprenderemos mais uma: congruence.

A tática lia faz uso de fatos sobre adição e multiplicação para provar igualdades. Uma maneira 
mais básica de tratar tais fórmulas é encarar cada função que aparece nelas como uma caixa-preta: 
nada se sabe sobre o comportamento da função. Com base apenas nas propriedades da própria igualdade, 
ainda é possível provar algumas fórmulas. Por exemplo, y = f x → g y = g (f x), mesmo que não 
saibamos nada sobre f ou g: *)

Theorem eq_example1 :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  intros. rewrite H. reflexivity.
Qed.

(* As propriedades essenciais da igualdade são que ela é:

  - reflexiva

  - simétrica

  - transitiva

  - uma congruência: ela respeita a aplicação de funções e predicados.

É essa propriedade de congruência que estamos usando quando fazemos rewrite na prova acima: se 
a = b, então f a = f b. (O capítulo ProofObjects explora essa ideia mais a fundo sob o nome de 
''igualdade de Leibniz''.)

A tática congruence é um procedimento de decisão para igualdade com funções não interpretadas e 
outros símbolos. *)

Theorem eq_example1' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  congruence.
Qed.

(* A tática congruence é capaz de trabalhar com construtores, tirando proveito inclusive da 
injetividade e da distinção deles. *)

Theorem eq_example2 : forall (n m o p : nat),
    (n, o) = (m, p) ->
    n = m.
Proof.
  congruence.
Qed.

Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
    nil <> h :: t.
Proof.
  congruence.
Qed.

(* Isso nos dá outra maneira de simplificar nossa prova de determinismo, que fica bem curta 
mesmo sem usar táticas personalizadas: *)

Theorem ceval_deterministic_congruence: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
    inversion E2; subst;
    auto;
    try congruence. (* <---- isso resolve 4 casos, anteriormente provados
                             por rewrite e discriminate *)
- (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
- (* E_WhileTrue, com b verdadeiro *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto.
Qed.

(* Exercício *)
(* Os exercícios abaixo poderiam ser provados com scripts de prova manuais (relativamente) longos, 
mas cada um pode ser resolvido com apenas uma única chamada de um solucionador automático que 
aprendemos (congruence ou lia). *)
Local Notation "x <= y" := (Peano.le x y) (at level 70, no associativity).

Theorem cons_equal : forall {X} (n m: X) (l: list X),
    n = m -> n :: l = m :: l.
Proof. 
  congruence.
Qed.

Theorem plus_le_cancel_r : forall n m p : nat,
    n + p <= m + p -> n <= m.
Proof.
  lia.
Qed.

Theorem no_half : forall n,
    2 * n <> 1.
Proof.
  lia.
Qed.

Theorem pair_equal : forall {X} (a b c d: X) (e: X * X),
    (a, (b, c)) = (d, e) ->
    e = (d, c) ->
    b = d.
Proof. 
  congruence.
Qed.