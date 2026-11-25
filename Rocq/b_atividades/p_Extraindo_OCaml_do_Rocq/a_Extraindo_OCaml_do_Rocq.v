(* Extração *)

(* Extraindo OCaml do Rocq *)

(************************************ Extração Básica *************************************)

(* Em sua forma mais simples, extrair um programa eficiente a partir de um escrito em Rocq 
é totalmente direto.

Primeiro, indicamos para qual linguagem queremos extrair. As opções são OCaml (a mais 
madura), Haskell (funciona na maior parte dos casos) e Scheme (um pouco desatualizada). *)

From Stdlib Require Extraction.
Set Extraction Output Directory ".".
Extraction Language OCaml.

(* Agora carregamos o ambiente do Rocq com algumas definições, seja diretamente ou 
importando-as de outros módulos. *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import EqNat.
Require Import LFPTBR.o_ImpCEvalFun.a_ImpCEvalFun.

(* Por fim, indicamos ao Rocq o nome de uma definição a ser extraída e o nome de um 
arquivo no qual o código extraído será colocado. *)

Extraction "imp1.ml" ceval_step.

(* Quando o Rocq processa esse comando, ele gera um arquivo imp1.ml contendo uma versão 
extraída de ceval_step, junto com tudo aquilo de que ela depende recursivamente. Compile o 
arquivo .v atual e dê uma olhada no imp1.ml agora.*)

(************************* Controlando a extração de tipos específicos ************************)

(* Podemos instruir o Rocq a extrair certas definições Inductive (indutivas) para tipos 
específicos em OCaml. Para cada uma delas, devemos especificar:

    - como o próprio tipo do Rocq deve ser representado em OCaml, e
    - como cada construtor deve ser traduzido. *)

Extract Inductive bool => "bool" [ "true" "false" ].

(* Além disso, para tipos que não são de enumeração (nos quais os construtores recebem 
argumentos), fornecemos uma expressão em OCaml que pode ser usada como um 'recursor' sobre os 
elementos do tipo. (Pense nos numerais de Church.) *)

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

(* Também podemos extrair constantes definidas para termos ou operadores específicos em OCaml. *)

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

(* Importante: é inteiramente sua responsabilidade garantir que as traduções que você está 
fornecendo fazem sentido. Por exemplo, pode ser tentador incluir esta:
    Extract Constant minus ⇒ "( - )".
mas fazer isso pode gerar uma confusão séria! (Por quê?) *)

Extraction "imp2.ml" ceval_step.

(* Dê uma olhada no arquivo imp2.ml. Observe como as definições fundamentais mudaram em relação 
ao imp1.ml. *)

(*************************************** Um Exemplo Completo **********************************)

(* Para usar nosso avaliador extraído para executar programas Imp, tudo o que precisamos 
adicionar é um pequeno programa principal (driver) que chama o avaliador e imprime o 
resultado.

Por simplicidade, vamos imprimir os resultados exibindo (dumping out) as quatro primeiras 
posições de memória no estado final.

Além disso, para facilitar a digitação de exemplos, vamos extrair um parser do módulo Rocq 
ImpParser. Para fazer isso, primeiro precisamos configurar a correspondência correta entre 
strings do Rocq e listas de caracteres do OCaml. *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

(* Também precisamos de mais uma variante de booleanos. *)

Extract Inductive sumbool => "bool" ["true" "false"].

(* A extração é a mesma de sempre. *)

Require Import LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.
Require Import LFPTBR.n_ImpParser.a_ImpParser.
Require Import LFPTBR.h_Mapas_Totais_e_Parciais.a_Mapas_Totais_e_Parciais.

Extraction "imp.ml" empty_st ceval_step parse.

(* Agora vamos executar nosso avaliador Imp gerado. Primeiro, dê uma olhada no arquivo 
impdriver.ml. (Este foi escrito à mão, não extraído.) 

Em seguida, compile o driver junto com o código extraído e execute-o, da seguinte forma:
    ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
    ./impdriver
(As flags -w passadas para o ocamlc servem apenas para suprimir alguns avisos espúrios/sem 
importância.)*)

(****************************************** Discussão *****************************************)

(* Como provamos que a função ceval_step se comporta da mesma forma que a relação ceval em um 
sentido apropriado, o programa extraído pode ser visto como um interpretador certificado de Imp. 
É claro que o parser que estamos usando não é certificado, já que não provamos nada sobre ele! *)

(**************************************** Indo Mais Longe *************************************)

(* Mais detalhes sobre extração podem ser encontrados no capítulo Extract em Verified 
Functional Algorithms (Volume 3 do Software Foundations). *)