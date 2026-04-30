1. Define `mult : Nat -> Nat -> Nat` and `factorial : Nat -> Nat` for `Natural` numbers.

2. Translate the following logical statements into types using Curry–Howard correspondence:
    - `P /\ (Q \/ R)`
    - `(P -> Q) -> R`
    - `~ ~ ~ P`

3. Does there exist a function of type `False -> P` for any and every `P`. Why? What does this fact correspond to in logic?

4. Try to prove the following propositions using the principle of induction: 
    - `forall n : Nat. n = n + 0`
    - `forall x y : List Nat. length (x ++ y) = length x + length y`
