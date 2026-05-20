(* Tipos em Rocq*)

(* Checagem de tipos*)

Check true.
(*true : bool *)

Check true: bool. (* Checa se true é booleano*)
Check (negb true) : bool.

(* negb é uma função. Os tipos de funções são chamados _function types_*)
Check negb : bool -> bool. (* Um tipo de função que recebe uma entrada cujo tipo deve ser bool e uma saída cujo tipo deve ser bool*)

(* Construindo novos tipos a partir de tipos antigos*)

Inductive rgb: Type :=
    | vermelho
    | verde
    | azul.


Inductive color: Type :=
   | preto
   | branco
   | primario (p: rgb). (* o primario carrega o dado adicional p cujo tipo obrigatoriamente deve ser rgb *)


(* Função que diz se cor é primária (preto ou branco)*)
Definition monocromatico (c: color) : bool :=
   match c with
   | preto => true
   | branco => true
   | primario p => false
   end.

(* Função que diz se a cor é vermelha*)
Definition e_vermelha (c: color) : bool :=
   match c with
   | preto => false
   | branco => false
   | primario vermelho => true (* primario carregando dado vermelho*)
   | primario _ => false (* primario carregando qualquer outro - usa-se o símbolo "_" - de dado *)
   end.