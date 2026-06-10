import Mathlib.Tactic
import Blaster

-- unit

structure BadQuantity where
  val : Float
  unit : String
  deriving Repr

def badMeter (x : Float) : BadQuantity := { val := x, unit := "m" }
def badKilo (x : Float) : BadQuantity := { val := x, unit := "kg" }

def badAdd (p : BadQuantity) (q : BadQuantity) : Option BadQuantity :=
  if p.unit == q.unit then some { val := p.val + q.val, unit := p.unit }
  else none

#eval badAdd (badMeter 2) (badKilo 2)

structure Quantity (unit : String) where
  val : Float
  deriving Repr

def meter (x : Float) : Quantity "m" := { val := x }
def kilo (x : Float) : Quantity "kg" := { val := x }
def meterpsec (x : Float) : Quantity "m/s" := { val := x }

def add {u : String} (p : Quantity u) (q : Quantity u) : Quantity u := { val := p.val + q.val }

#eval add (meter 2) (meter 4)
-- #eval add (meter 2) (kilo 4)

def km2m (p : Quantity "km") : Quantity "m" := { val := p.val * 1000 }

def time (d : Quantity "m") (s : Quantity "m/s") : Quantity "s" := { val := d.val / s.val }

#eval time (km2m ({ val := 2 } : Quantity "km")) (meterpsec 1)

---

#check [Nat, Int].head?

inductive Vec (a : Type u) : (n : Nat) -> Type u where
  | nil : Vec a 0
  | cons {n} : a -> Vec a n -> Vec a (n + 1)

namespace Vec

def v2l : Vec a n -> List a
  | Vec.nil       => []
  | Vec.cons x xs => x :: v2l xs

def l2v : (xs : List a) -> Vec a (xs.length)
  | []      => Vec.nil
  | y :: ys => Vec.cons y (l2v ys)

def head : Vec a (n + 1) -> a
  | .cons x _ => x

def tail : Vec a (n + 1) -> Vec a n
  | .cons _ xs => xs

-- def badAppend (xs : Vec a m) (ys : Vec a n) : Vec a (m + n) :=
--   match ys with
--   | Vec.nil => xs
--   | Vec.cons z zs => .cons z (badAppend xs zs)

-- def okayAppend (xs : Vec a m) (ys : Vec a n) : Vec a (m + n) :=
--   match xs with
--   | Vec.nil => ys
--   | Vec.cons z zs => .cons z (okayAppend zs ys) -- ((m - 1) + n) + 1

def goodAppend : {m n : Nat} -> Vec a m -> Vec a n -> Vec a (m + n)
  | 0, n, .nil, ys => by
    have h : n = 0 + n := by simp
    exact h ▸ ys
  | m + 1, n, .cons x xs, ys => by
    have h : (m + 1) + n = (m + n) + 1 := by
      calc
        (m + 1) + n = m + (1 + n) := by rw [Nat.add_assoc]
        _ = m + (n + 1) := by rw [Nat.add_comm 1 n]
        _ = (m + n) + 1 := by rw [Nat.add_assoc]
    exact h ▸ .cons x (goodAppend xs ys)

def u : Vec String 2 := .cons "cherry" (.cons "mango" .nil)
def v : Vec String 3 := .cons "apple" (.cons "orange" (.cons "plum" Vec.nil))
def l : List a := []

#eval goodAppend u v

---

structure Fini (n : Nat) where
  nval : Nat
  prf : nval < n

def x : Fini 112 := { nval := 0, prf := by norm_num }

def fini2nat (f : Fini n) : Nat := f.nval

#eval fini2nat x

def get : Vec a n -> (i : Fini n) -> a
  | .cons x _, ⟨0, _⟩ => x
  | .cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, Nat.lt_of_succ_lt_succ h⟩
