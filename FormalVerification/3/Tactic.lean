theorem modus_ponens (P Q : Prop) : (P -> Q) -> P -> Q := by
  intro f p
  exact (f p)

theorem conj_term (P Q R T : Prop) : P -> Q -> (P -> R) -> (Q -> T) -> (R ∧ T) := λ p q f g =>
  And.intro (f p) (g q)

theorem conj_tactic (P Q R T : Prop) : P -> Q -> (P -> R) -> (Q -> T) -> (R ∧ T) := by
  intro p q f g
  constructor
  · exact (f p)
  · exact (g q)

theorem case_cons (P Q R T : Prop) : (P ∧ Q) -> (P -> R) -> (Q -> T) -> (R ∧ T) := by
  intro pq f g
  cases pq with
    | intro p q =>
      constructor
      · exact (f p)
      · exact (g q)

theorem modus_tollens (P Q : Prop) : (P -> Q) -> ¬ Q -> ¬ P := by
  intro f nq
  unfold Not at *
  intro p
  exact (nq (f p))

theorem dni (P : Prop) : P -> ¬ (¬ P) := by
  intro p np
  unfold Not at *
  exact (np p)

theorem dne (P : Prop) : ¬ (¬ P) -> P := by
  unfold Not
  have lem := Classical.em P
  cases lem with
  | inl p => exact (λ _ => p)
  | inr np =>
    intro h
    unfold Not at np
    exfalso
    exact (h np)

-- natural
theorem add_zero_left (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    have h : 0 + (n + 1) = (0 + n) + 1 := by exact (Nat.add_assoc 0 n 1)
    rw [h]
    rw [ih]

theorem add_zero_left_simp (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp

theorem add_commutative (x y : Nat) : x + y = y + x := by
  induction x generalizing y with
  | zero => simp
  | succ z ih => simp [Nat.succ_add, Nat.add_assoc, ih y]
