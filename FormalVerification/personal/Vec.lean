import Mathlib.Tactic
import Blaster

inductive Vec (a : Type u) : (n : Nat) -> Type u where
  | nil  : Vec a 0
  | cons {n} : a -> Vec a n -> Vec a (n + 1)

namespace Vec
def v2l : Vec a n -> List a
  | .nil => []
  | .cons x xs => x :: v2l xs

def l2v : (xs : List a) -> Vec a (xs.length)
  | []      => .nil
  | y :: ys => .cons y (l2v ys)

def head : Vec a (n + 1) -> a
  | .cons x _ => x

def tail : Vec a (n + 1) -> Vec a n
  | .cons _ xs => xs

def appendR (xs : Vec a m) (ys : Vec a n) : Vec a (m + n) := match ys with
  | .nil => xs
  | .cons z zs => .cons z (appendR xs zs)

def appendL_hard : { m n : Nat } -> Vec a m -> Vec a n -> Vec a (m + n)
  | 0, n, .nil, ys           => by
    have h : 0 + n = n := by simp
    exact h.symm ▸ ys
  | m + 1, n, .cons x xs, ys => by
    have h : (m + 1) + n = (m + n) + 1 := by
      calc
        (m + 1) + n = m + (1 + n) := by rw [Nat.add_assoc]
        _ = m + (n + 1) := by rw [Nat.add_comm 1 n]
        _ = (m + n) + 1 := by rw [Nat.add_assoc]
    exact h ▸ .cons x (appendL_hard xs ys)

def appendL_simp : { m n : Nat } -> Vec a m -> Vec a n -> Vec a (m + n)
  | 0, n, .nil, ys           => by exact (by simp : n = 0 + n) ▸ ys
  | m1 + 1, n, .cons x xs, ys => by 
    have h : (m1 + 1) + n = (m1 + n) + 1 := by simp [Nat.add_assoc, Nat.add_comm 1 n]
    exact h ▸ .cons x (appendL_simp xs ys)

infixl:65 " +++ " => Vec.appendL_simp

def reverseList : List a -> List a
  | [] => []
  | x :: xs =>
    let rec go : List a -> List a -> List a
      | acc, [] => acc
      | acc, (y :: ys) => go (y :: acc) ys
    go [] (x :: xs)


def reverseVec : Vec a n -> Vec a n
  | .nil => .nil
  | .cons x xs => reverseVec xs +++ .cons x .nil

def reverse : {n : Nat} -> Vec a n -> Vec a n
  | _, .nil => .nil
  | n1 + 1, .cons x xs =>
    let rec go : (k m : Nat) -> Vec a k -> Vec a m -> Vec a (k + m)
      | _, 0, acc, .nil => acc
      | k, m1 + 1, acc, .cons y ys => by
        have h : k + (m1 + 1) = (k + 1) + m1 := by rw [Nat.add_assoc, Nat.add_comm m1 1]
        exact h ▸ go (k + 1) m1 (Vec.cons y acc) ys
    by
      have h : n1 + 1 = 0 + (n1 + 1) := by simp
      exact h ▸ go 0 (n1 + 1) .nil (.cons x xs)

def l : List String := ["apple", "orange", "plum"]
def v : Vec String 3 := .cons "apple" (.cons "orange" (.cons "plum" .nil))
def u : Vec String 3 := .cons "banana" (.cons "cherry" (.cons "guava" .nil))

#eval v2l v
#eval l2v l
#eval v.tail
#eval v.head
#eval v +++ u.reverse

---

structure Fini (n : Nat) where
  val : Nat
  prf : val < n

#check (⟨0, by norm_num⟩ : Fin 5)

def Fini.toNat (n : Nat) (f : Fin n) : Nat := f.val

def Fin.range (n : Nat) : List (Fin n) :=
  match n with
  | 0     => []
  | n + 1 => ⟨n, by omega⟩ :: (Fin.range n).map (fun ⟨i, h⟩ => ⟨i, by omega⟩)

def get : Vec a n -> Fin n -> a
  | .cons x _,  ⟨0,     _⟩ => x
  | .cons _ xs, ⟨i + 1, h⟩ => Vec.get xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

#eval v.get ⟨0, by norm_num⟩   -- "apple"
#eval v.get ⟨1, by norm_num⟩   -- "orange"
#eval v.get ⟨2, by norm_num⟩   -- "plum"
-- #eval v.get ⟨3, by norm_num⟩
-- #eval v.get ⟨100, by norm_num⟩

def set : Vec a n -> Fin n -> a -> Vec a n
  | .cons _ xs, ⟨0,     _⟩, y => .cons y xs
  | .cons x xs, ⟨i + 1, h⟩, y => .cons x (Vec.set xs ⟨i, Nat.lt_of_succ_lt_succ h⟩ y)

#eval v2l (v.set ⟨0, by norm_num⟩ "mango")
#eval v2l (v.set ⟨2, by norm_num⟩ "mango")

#eval v2l (v.set ⟨0, by norm_num⟩ "mango" |>.set ⟨1, by norm_num⟩ "kiwi")

-- #eval v.set ⟨3, by norm_num⟩ "mango"
-- #eval v.set ⟨100, by norm_num⟩ "mango"

def getUnsafe : Vec a n -> Nat -> Option a
  | .cons x _,  0     => some x
  | .cons _ xs, i + 1 => Vec.getUnsafe xs i
  | .nil,       _     => none

#eval v.getUnsafe 100

end Vec

---

structure Quantity (unit : String) where
  val : Float
  deriving Repr

def m (x : Float) : Quantity "m" := ⟨x⟩
def km (x : Float) : Quantity "km" := ⟨x⟩
def s (x : Float) : Quantity "s" := ⟨x⟩
def kg (x : Float) : Quantity "kg" := ⟨x⟩
def mps (x : Float) : Quantity "m/s" := ⟨x⟩

namespace Quantity

def add (p q : Quantity u) : Quantity u := ⟨p.val + q.val⟩

def km2m (k : Quantity "km") : Quantity "m" := ⟨k.val * 1000⟩

def time (d : Quantity "m") (v : Quantity "m/s") : Quantity "s" := { val := d.val / v.val }

#eval time (m 10) (mps 2)
-- #eval time (km 10) (mps 2)
#eval time (km2m (km 10)) (mps 2)
  
def binarySearch (xs : Vec Int n) (z : Int) (lo hi : Fin (n + 1)) : Option (Fin n) :=
  if h : lo.val >= hi.val then
    none
  else
    let mid : Fin (n + 1) := ⟨(lo.val + hi.val) / 2, by omega⟩
    if hmid : mid.val < n then
      let midVal := xs.get ⟨mid.val, hmid⟩
      if midVal == z then
        some ⟨mid.val, hmid⟩
      else if midVal < z then
        binarySearch xs z ⟨mid.val + 1, by omega⟩ hi
      else
        binarySearch xs z lo ⟨mid.val, by omega⟩
    else
      none
termination_by hi.val - lo.val
