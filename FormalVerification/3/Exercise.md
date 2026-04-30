1. Given `P Q R : Prop`, prove the following theorems:
  - `P ∧ Q -> Q ∧ P`
  - `P ∨ Q -> (¬ P) -> Q`
  - `P ∨ Q -> (P -> R) -> (Q -> R) -> R`

2. Given `P Q R : Prop`, prove the De Morgan Law (you may need `Classical.em` in one of these):
  - `¬ (P ∧ Q) <-> ¬ P ∨ ¬ Q`
  - `¬ (P ∨ Q) <-> ¬ P ∧ ¬ Q`

3. Given `a b c : Nat`, prove the following theorems:
  - `a + 1 = 1 + a`
  - `a * 0 = 0`
  - `a * b = b * a`
  - `a * (b + c) = a * b + a * c`

4. Given `a b : Bool`, prove the following theorems:
  - `a && b = b && a`
  - `not (not a) = a`
  - `not (a || b) = not a && not b`

5. Given `a b : List a`, prove the following theorems:
  - `(x ++ y).length = x.length + y.length`
  - `(reverse x).length = x.length`
  - `x.reverse.reverse = x`
