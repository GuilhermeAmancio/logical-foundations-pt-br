Require Import List.
Import ListNotations.

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