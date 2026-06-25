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