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

    
    

    

    
    
    
    

