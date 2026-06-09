import Mathlib.Tactic

-- irrelevance
theorem p : 1 < 2 := by decide

theorem q : 1 < 2 := by simp

theorem proof_eql (P : Prop) (p : P) (q : P) : p = q := by rfl

-- modus tollens
theorem modus_tollens (P Q : Prop) : (P -> Q) -> ¬ Q -> ¬ P := by
  unfold Not -- not really needed
  intro h nq p
  exact (nq $ h p)

-- de Morgan (requires `Classical` in next leg)
theorem de_morgan_1 (P Q : Prop) : ¬ (P ∨ Q) <-> (¬ P ∧ ¬ Q) := by
  unfold Not
  constructor
  . intro h
    exact ⟨fun p => h (Or.inl p), fun q => h (Or.inr q)⟩
  . intro ⟨np, nq⟩ pvq
    cases pvq with
    | inl p => exact np p
    | inr q => exact nq q

theorem de_morgan_2 (P Q : Prop) : ¬ (P ∧ Q) <-> (¬ P ∨ ¬ Q) := by
  unfold Not
  constructor
  . intro h
    -- have lem (A : Prop) : A ∨ ¬ A := Classical.em A
    cases Classical.em P with
    | inl p => exact Or.inr (λ q => h ⟨p, q⟩)
    | inr np => exact Or.inl np
  . intro npvnq 
    cases npvnq with
    | inl np => exact (λ ⟨p, q⟩ => np p)
    | inr nq => exact (λ ⟨p, q⟩ => nq q)

-- double negation
theorem dni (P : Prop) : P -> ¬ (¬ P) := by
  unfold Not
  intro p np
  exact np p

theorem dne (P : Prop) : ¬ (¬ P) -> P := by
  unfold Not
  cases Classical.em P with
  | inl p => exact (λ _ => p)
  | inr np =>
    intro h
    exfalso
    exact (h np)

-- structural

-- numbers
theorem add_commu (x y : Nat) : x + y = y + x := by
  induction x with
  | zero => simp
  | succ x xih => simp [Nat.succ_add, xih, Nat.add_assoc]

def sum_till : Nat -> Nat
  | 0 => 0
  | n + 1 => n + 1 + sum_till n

#eval sum_till 5

theorem sum_till_n_simp (n : Nat) : 2 * sum_till n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n nih =>
    calc
      2 * (n + 1 + sum_till n) = 2 * (n + 1) + (2 * sum_till n) := by simp [Nat.mul_add]
      _ = 2 * (n + 1) + n * (n + 1) := by rw [nih]
      _ = (2 + n) * (n + 1) := by simp [Nat.mul_comm, Nat.mul_add]
      _ = (n + 2) * (n + 1) := by simp [Nat.add_comm]
      _ = (n + (1 + 1)) * (n + 1) := by rfl
      _ = (n + 1) * (n + 1 + 1) := by simp [Nat.mul_comm]

theorem sum_till_n_lin (n : Nat) : 2 * sum_till n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n nih =>
    simp [sum_till]
    linarith

-- lists
namespace List

theorem len_append (xs ys : List a) :
  (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil  => simp
  | cons x xs xih =>
    dsimp
    rw [xih]
    simp [Nat.add_right_comm] -- rw [Nat.add_right_comm xs.length 1 ys.length]

def revn : List a -> List a
  | [] => []
  | x :: xs => revn xs ++ [x]

theorem revn_append (xs ys : List a) : (xs ++ ys).revn = ys.revn ++ xs.revn := by
  induction xs with
  | nil => simp [revn]
  | cons x xs xih =>
    simp [revn, xih]

theorem dbl_revn (xs : List a) : xs.revn.revn = xs := by
  induction xs with
  | nil => rfl
  | cons x xs xih =>
    simp [revn]
    rw [revn_append xs.revn [x]]
    simp [revn, xih]

def rev : List a -> List a
  | [] => []
  | x :: xs =>
    let rec go : List a -> List a -> List a
      | acc, [] => acc
      | acc, (y :: ys) => go (y :: acc) ys
    go [] (x :: xs)

theorem rev_eq (xs : List a) : revn xs = rev xs := by
  have h (ys : List a) : (acc : List a) -> rev.go acc ys = ys.revn ++ acc := by
   induction ys with 
   | nil => simp [revn, rev.go]
   | cons z zs zih =>
    intro acc
    simp [revn, rev.go]
    rw [zih (z :: acc)]
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [revn, rev]
    simp [h, revn]
