(* Pares de Números *)
 
Inductive produto_cartesiano_nat : Type :=
   | par (n1 n2 : nat).

Check (par 3 5) : produto_cartesiano_nat.

Definition primeiro (p: produto_cartesiano_nat) : nat :=
   match p with
   | par x y => x
   end.

Definition segundo (p: produto_cartesiano_nat ) : nat :=
   match p with
   | par x y => y
   end.

Compute (primeiro (par 3 5)).
(* = 3  : nat *)
