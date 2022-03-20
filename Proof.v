Section foo.

(* Write your proof terms in place of underscores below ("_") *)

Variables A B C : Prop.

(* Exercise 1: Prove implication is transitive. What does this logical lemma correspond to in functional programming? *)
Check
  (fun a b x => b (a x))
: (A -> B) -> (B -> C) -> (A -> C).

(* Exercise 2: Prove conjunction is associative *)
Check
  (fun x => conj (proj1 (proj1 x)) (conj (proj2 (proj1 x)) (proj2 x)))
: (A /\ B) /\ C -> A /\ (B /\ C).

(* Exercise 3: Prove disjunction distributes over conjunction: *)
Check
  (fun x => 
  match x with 
    | or_introl a => conj (or_introl a) (or_introl a)
    | or_intror b => conj (or_intror (proj1 b)) (or_intror (proj2 b))
    end)
: A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).

(* Exercise 4: Prove weak form of Peirce's law holds in intuitionistic logic *)
Check
  (fun q => q (fun p => p (fun a => q (fun aba => a))))
: ((((A -> B) -> A) -> A) -> B) -> B.

(* Exercise 5: We can always add double negation (but cannot drop it in general) *)
Check
  (fun a => (fun f => f a))
: A -> ~ ~ A.

(* Exercise 6: Although we can in some special cases like the following: *)
Check
  (fun g => (fun a => g (fun f => f a)))
: ~ ~ ~ A -> ~ A.

(* Exercise 7: Prove we cannot add the negation of the law of excluded middle and have a sound logic.
   Keep in mind that "~ A" means "A -> False" *)
Check
  (fun f => f (or_intror (fun a => f (or_introl a))))
: ~ ~ (A \/ ~ A).