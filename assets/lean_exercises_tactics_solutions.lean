-- SOLUTIONS: Lean4 Proof Progression
-- make sure you have the necessary imports if you want to work in this file. 

-- LEVEL 1: Basic Logic (using only intro, exact, assumption)

theorem ex1_identity (P : Prop) (h : P) : P := by
  exact h

theorem ex2_modus_ponens (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  apply h2
  exact h1

theorem ex3_chain (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  apply h2
  apply h1
  exact h3

theorem ex4_function_composition (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro h1 h2 h3
  apply h2
  apply h1
  exact h3


-- LEVEL 2: Conjunctions (using constructor, cases)

theorem ex5_make_and (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

theorem ex6_and_left (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | mk hp hq => exact hp

theorem ex7_and_right (P Q : Prop) (h : P ∧ Q) : Q := by
  cases h with
  | mk hp hq => exact hq

theorem ex8_and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | mk hp hq => 
    constructor
    · exact hq
    · exact hp


-- LEVEL 3: Disjunctions (using left, right, cases)

theorem ex9_or_intro_left (P Q : Prop) (h : P) : P ∨ Q := by
  left
  exact h

theorem ex10_or_intro_right (P Q : Prop) (h : Q) : P ∨ Q := by
  right
  exact h

theorem ex11_or_swap (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => 
    right
    exact hp
  | inr hq => 
    left
    exact hq

theorem ex12_or_and_distribute (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  cases h with
  | mk hp hqr =>
    cases hqr with
    | inl hq =>
      left
      constructor
      · exact hp
      · exact hq
    | inr hr =>
      right
      constructor
      · exact hp
      · exact hr


-- LEVEL 4: Negation (using intro for ¬, exfalso, contradiction)

theorem ex13_not_intro (P : Prop) (h : P → False) : ¬P := by
  exact h

theorem ex14_double_negation (P : Prop) (h : P) : ¬¬P := by
  intro hnp
  apply hnp
  exact h

theorem ex15_contradiction_rule (P Q : Prop) (h1 : P) (h2 : ¬P) : Q := by
  exfalso
  apply h2
  exact h1

theorem ex16_modus_tollens (P Q : Prop) (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  intro hp
  apply h2
  apply h1
  exact hp


-- LEVEL 5: Classical Logic (using Classical.by_contradiction)

theorem ex17_excluded_middle (P : Prop) : P ∨ ¬P := by
  Classical.by_contradiction h
  apply h
  right
  intro hp
  apply h
  left
  exact hp

theorem ex18_double_neg_elim (P : Prop) (h : ¬¬P) : P := by
  Classical.by_contradiction hnp
  apply h
  exact hnp

theorem ex19_contrapositive (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro hnq hp
  apply hnq
  apply h
  exact hp


-- LEVEL 6: Equality (using rfl, rw, simp)

theorem ex20_equality_refl (a : Nat) : a = a := by
  rfl

theorem ex21_equality_substitute (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

theorem ex22_add_zero (n : Nat) : n + 0 = n := by
  simp

theorem ex23_zero_add (n : Nat) : 0 + n = n := by
  simp


-- LEVEL 7: Simple Arithmetic (using simp, linarith if needed)

theorem ex24_add_comm (a b : Nat) : a + b = b + a := by
  simp [Nat.add_comm]

theorem ex25_add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simp [Nat.add_assoc]

theorem ex26_simple_inequality (n : Nat) (h : n > 5) : n ≥ 3 := by
  linarith


-- LEVEL 8: Existentials (using use, cases with intro)

theorem ex27_exists_intro (n : Nat) : ∃ m, m > n := by
  use n + 1
  simp

theorem ex28_exists_elim (P : Nat → Prop) (h : ∃ n, P n) : ∃ m, P m := by
  cases h with
  | intro n hn =>
    use n
    exact hn

def Even (n : Nat) : Prop := ∃ k, n = 2 * k

theorem ex29_even_intro : Even 6 := by
  use 3
  simp

theorem ex30_even_sum (n m : Nat) (hn : Even n) (hm : Even m) : Even (n + m) := by
  cases hn with
  | intro k1 hk1 =>
    cases hm with
    | intro k2 hk2 =>
      use k1 + k2
      rw [hk1, hk2]
      ring


-- BONUS CHALLENGE: The original theorem

theorem ex31_even_pos_ge_two (n : Nat) (h1 : n > 0) (h2 : Even n) : n ≥ 2 := by
  cases h2 with
  | intro k hk =>
    -- We have n = 2 * k and n > 0
    -- So 2 * k > 0, which means k > 0 (since k is Nat)
    -- Therefore k ≥ 1, so 2 * k ≥ 2
    have hk_pos : k > 0 := by
      Classical.by_contradiction h_contra
      simp at h_contra
      rw [hk] at h1
      simp [h_contra] at h1
    -- Since k > 0 and k is Nat, we have k ≥ 1
    have hk_ge_one : k ≥ 1 := Nat.succ_le_iff.mpr hk_pos
    -- Therefore 2 * k ≥ 2 * 1 = 2
    rw [hk]
    linarith [hk_ge_one]
