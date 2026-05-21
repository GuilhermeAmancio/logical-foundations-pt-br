Require Import Nat.

(* Mais Exercícios *)
Theorem identidade_fn_aplicada_duas_vezes :
   forall (f : bool -> bool),
   (forall (x : bool), f x = x)->
   forall (b : bool), f (f b) = b.

Proof.
    intros f b x.
    rewrite -> b. rewrite b. reflexivity.
Qed.

(****************************************)

Theorem negacao_identidade_fn_aplicada_duas_vezes :
   forall (f : bool -> bool),
   (forall (x : bool), f x = negb x)->
   forall (b : bool), f (f b) = b.

Proof.
    intros f H b.
    rewrite H. rewrite H.
     destruct b.
     - reflexivity.
     - reflexivity. 
    Qed.

(*****************************************)

Theorem andb_eq_orb :
   forall (b c : bool),
   (andb b c = orb b c) -> b = c.

Proof.
    intros b c H.
    -destruct b.
    {destruct c.
       - reflexivity.
       - simpl in H. rewrite -> H. reflexivity. }
    {destruct c.
        - simpl in H. rewrite H. reflexivity. 
        - reflexivity. }
Qed.

(* Exercício das provas comp penalidade por atrasos *)

Module DiasDeAtraso.

Inductive letra : Type :=
   | A | B | C | D | F. (* Notas *)

 Inductive modificador : Type :=
    | Mais | Natural | Menos. 

Inductive nota : Type :=
   Nota (l: letra)(m:modificador). (* Ex: Nota A Menos *)

Inductive comparacao : Type :=
   | Ig (* Igual *)
   | Meq (* Menor que *)
   | Maq. (* Maior que *)
   
Definition comparacao_letra (l1 l2 : letra) : comparacao :=
   match l1, l2 with
   | A, A => Ig
   | A, _ => Maq
   | B, A => Meq
   | B, B => Ig
   | B, _ => Maq
   | C, (A | B) => Meq
   | C, C => Ig
   | C, _ => Maq
   | D, (A | B | C) => Meq
   | D, D => Ig
   | D, _ => Maq
   | F, (A | B | C | D) => Meq
   | F, F => Ig
   end.

(* Exemplo de testes *)
Compute comparacao_letra B A.
Compute comparacao_letra D D.
Compute comparacao_letra B F.

(* Provando que a função comparacao_prova  dá Eq como resultado quando comparando p consigo mesma *)
Theorem comparacao_letra_Ig :
   forall p, comparacao_letra p p = Ig.

Proof.
   intros p.
   destruct p eqn: Ep. 
   - Compute (comparacao_letra A A). reflexivity.
   - Compute (comparacao_letra B B). reflexivity.
   - Compute (comparacao_letra C C). reflexivity. 
   - Compute (comparacao_letra D D). reflexivity.
   - Compute (comparacao_letra F F). reflexivity. 
Qed.

Definition comparador_de_modificacao (m1 m2 : modificador) : comparacao := 
   match m1, m2 with
   | Mais, Mais => Ig
   | Mais, _ => Maq
   | Natural, Mais => Meq
   | Natural, Natural => Ig
   | Natural, _ => Maq
   | Menos, (Mais | Natural) => Meq
   | Menos, Menos => Ig
   end.

Definition comparacao_nota (n1 n2 : nota) : comparacao :=
   match n1, n2 with
   | Nota l1 m1 , Nota l2 m2 =>
     match comparacao_letra l1 l2 with
       | Ig => comparador_de_modificacao m1 m2
       | Maq => Maq
       | Meq => Meq
       end
   end.

Example nota_teste_comparacao1 :
(comparacao_nota (Nota A Menos)(Nota B Mais)) = Maq.
Proof.
simpl. reflexivity. Qed.

Example nota_teste_comparacao2 :
(comparacao_nota (Nota A Menos)(Nota A Mais)) = Meq.
Proof.
simpl. reflexivity. Qed.

Example nota_teste_comparacao3 :
(comparacao_nota (Nota F Mais)(Nota F Mais)) = Ig.
Proof.
simpl. reflexivity. Qed.

Example nota_teste_comparacao4 :
(comparacao_nota (Nota B Menos)(Nota C Mais)) = Maq.
Proof.
simpl. reflexivity. Qed.

(* Definindo as penalidades por atraso *)
Definition diminui_letra(l : letra) : letra :=
   match l with
   | A => B
   | B => C 
   | C => D
   | D => F
   | F => F (* Não dá para abaixar F *)
   end.

(* Temos o problema do caso que F precisa ser abaixado, já que ele é o menor valor. Esse é o teorema corrigido para esse caso *)

Theorem diminui_letra_prova:
   forall (l : letra),
   comparacao_letra F l = Meq ->
   comparacao_letra (diminui_letra l)l = Meq.

Proof.
   intros l H.
   destruct l.
   - simpl. reflexivity.
   - simpl. reflexivity.
   - simpl. reflexivity.
   - simpl. reflexivity.
   - rewrite <- H. simpl. reflexivity.
Qed.

Definition diminui_nota (n : nota) : nota :=
   match n with 
   | Nota l1 m1 =>  if (match l1, m1 with F, Menos => true
                       | _ , _ => false end) 
                        then Nota F Menos
                          else match m1 with
                                | Mais => Nota l1 Natural
                                | Natural => Nota l1 Menos
                                | Menos => Nota (diminui_letra l1) Mais
                               end
   end.
   
Example diminui_nota_A_Mais:
   diminui_nota (Nota A Mais) = (Nota A Natural).
Proof.
simpl. reflexivity. Qed.

Example diminui_nota_A_Natural:
   diminui_nota (Nota A Natural) = (Nota A Menos).
Proof.
simpl. reflexivity. Qed.

Example diminui_nota_A_Menos:
   diminui_nota (Nota A Menos) = (Nota B Mais).
Proof.
simpl. reflexivity. Qed.

Example diminui_nota_B_Mais:
   diminui_nota (Nota B Mais) = (Nota B Natural).
Proof.
simpl. reflexivity. Qed.

Example diminui_nota_F_Natural:
   diminui_nota (Nota F Natural) = (Nota F Menos).
Proof.
simpl. reflexivity. Qed.

Example diminui_nota_duas_vezes:
   diminui_nota (diminui_nota (Nota B Menos)) = (Nota C Natural).
Proof.
simpl. reflexivity. Qed.

Example diminui_nota_tres_vezes:
   diminui_nota (diminui_nota (diminui_nota (Nota B Menos))) = (Nota C Menos).
Proof.
simpl. reflexivity. Qed.

(* O Rocq não distingue exemplos de teoremas, então o exemplo abaixo é declarado como teorema para possível uso futuro *)
Theorem diminui_nota_F_Menos:
   diminui_nota (Nota F Menos) = (Nota F Menos).
 Proof.
 simpl. reflexivity. Qed.

(* Exercício : provar que diminui_nota realmente diminui a nota, com exceção de F Menos *)
Theorem diminui_nota_realmente_diminui:
   forall (n : nota),
   comparacao_nota (Nota F Menos) n = Meq ->
   comparacao_nota (diminui_nota n) n = Meq.

Proof.
   intros n H.
   destruct n as [l m].
   destruct m.
   - destruct l.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   - destruct l.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   - destruct l.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + simpl. reflexivity.
   + rewrite <- H. rewrite <- diminui_nota_F_Menos. simpl. reflexivity.
Qed.


Definition aplicar_politica_de_atraso (dias_atraso : nat) (n : nota) : nota :=
   if dias_atraso <? 9 then n
   else if dias_atraso <? 17 then diminui_nota n
   else if dias_atraso <? 21 then  diminui_nota (diminui_nota n)
   else diminui_nota (diminui_nota (diminui_nota n)).

Theorem aplicar_politica_de_atraso_unfold :
   forall (dias_atraso: nat) (n: nota),
   (aplicar_politica_de_atraso dias_atraso n) =
   (if dias_atraso <? 9 then n else
     if dias_atraso <? 17 then diminui_nota n else 
       if dias_atraso <? 21 then diminui_nota(diminui_nota n) 
         else diminui_nota (diminui_nota (diminui_nota n))).

Proof.
   intros. reflexivity.
Qed.

(* Exercício *)

Theorem sem_penalidade_sendo_pontual :
   forall (dias_atraso : nat) (n : nota),
   (dias_atraso <? 9 = true) ->
   aplicar_politica_de_atraso dias_atraso n = n.

Proof.
   intros dias_atraso n H.
   rewrite aplicar_politica_de_atraso_unfold.
   rewrite H.
   reflexivity.  
Qed.

Theorem uma_penalidade :
   forall (dias_atraso : nat) (n : nota),
   (dias_atraso <? 9 = false) -> 
   (dias_atraso <? 17 = true) ->
   aplicar_politica_de_atraso dias_atraso n = diminui_nota n.

Proof.
   intros dias_atraso n H1 H2.
   rewrite aplicar_politica_de_atraso_unfold.
   rewrite H1.
   rewrite H2.
   reflexivity.  
Qed.

End DiasDeAtraso.

(* Números Binários *)

Inductive bin : Type :=
   | Z
   | B0 (b : bin)
   | B1 (b : bin).

Fixpoint incr (m : bin) : bin :=
   match m with
   | Z => B1 Z
   | B0 x => B1 x
   | B1 x => B0 (incr x)
   end.

Fixpoint bin_para_nat (m:bin) : nat :=
   match m with
   | Z => 0
   | B0 x => mult 2 (bin_para_nat x)
   | B1 x => (mult 2 (bin_para_nat x)) + 1
   end.

Example teste_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
simpl. reflexivity. Qed.

Example teste_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
simpl. reflexivity. Qed.

Example teste_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
simpl. reflexivity. Qed.

Example teste_bin_incr4 : bin_para_nat(B0(B1 Z)) = 2.
Proof.
simpl. reflexivity. Qed.

Example teste_bin_incr5 : bin_para_nat(incr (B1 Z)) = 1 + bin_para_nat(B1 Z).
Proof.
simpl. reflexivity. Qed.

Example teste_bin_incr6 : bin_para_nat(incr (incr (B1 Z))) = 2 + bin_para_nat(B1 Z).
Proof.
simpl. reflexivity. Qed.

Example teste_bin_incr7 : bin_para_nat(B0(B0(B0(B1 Z)))) = 8.
Proof.
simpl. reflexivity. Qed.