Inductive rgb: Type :=
    | vermelho
    | verde
    | azul.


(* Module - Declaração cria espaço de nomes separados*)

Module ZonaDeExploracao.
    Definition b: rgb := azul.
End ZonaDeExploracao.

Definition b : bool := true.

(* Dentro do módulo ZonaDeExploracao b é do tipo rgb, fora é do tipo bool*)

Check ZonaDeExploracao.b : rgb.
Check b : bool.

(**************************************************************)

(* Tuplas (ou n-uplas)*)
(* Um construtor com múltiplos parâmetros pode ser usado para criar um tipo tupla*)

(* Criando o tipo nybble -- nybble são 4 bits*)

Inductive bit : Type :=
   | B1
   | B0.

Inductive nybble : Type :=
   | bits (bo b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
   : nybble.

(* Função para saber se todos os bits de um nybble são 0 -- por casamento de padrões *)

Definition TudoZero (nb : nybble) : bool :=
   match nb with
   | (bits B0 B0 B0 B0) => true
   | (bits _ _ _ _) => false    (* '_' signfica qualquer outra coisa *)
   end.

Compute (TudoZero (bits B1 B0 B1 B0)).
(* = false : bool*)

Compute (TudoZero (bits B0 B0 B0 B0)).
(* = true : bool*)
