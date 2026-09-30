import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    calc
      x ≤  0 := by apply (le_of_lt h)
      _ ≤ -x := by apply neg_nonneg.mpr (le_of_lt h)

theorem neg_le_abs (x : ℝ) : -x ≤ |x| := by
  have h : -x ≤ |(-x)| := le_abs_self (-x)
  rw [abs_neg] at h
  exact h

theorem abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  apply abs_le'.mpr
  constructor
  · linarith [(le_abs_self x), (le_abs_self y)]
  · linarith [(neg_le_abs x), (neg_le_abs y)]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left; exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  · rw [abs_of_neg h]
    constructor
    · intro h'
      right; exact h'
    · intro h'
      rcases h' with h' | h'
      · linarith
      · exact h'

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      exact h'.right
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h0 | h1⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x-1) * (x+1) = 0 := by
    calc
      (x-1) * (x+1) = x^2 - 1 := by ring
      _ = 0 := by rw [h, sub_self]
  apply mul_eq_zero.mp at h'
  rcases h' with h0 | h1
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x-y) * (x+y) = 0 := by
    calc
      (x-y) * (x+y) = x^2 - y^2 := by ring
      _ = 0 := by rw [h, sub_self]
  apply mul_eq_zero.mp at h'
  rcases h' with h0 | h1
  · left; linarith
  · right; linarith
section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x-1) * (x+1) = 0 := by
    calc
      (x-1) * (x+1) = x^2 - 1 := by ring
      _ = 0 := by rw [h, sub_self]
  apply mul_eq_zero.mp at h'
  rcases h' with h0 | h1
  · left
    exact sub_eq_zero.mp h0
  · right
    apply sub_eq_zero.mp
    simpa using h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x-y) * (x+y) = 0 := by
    calc
      (x-y) * (x+y) = x^2 - y^2 := by ring
      _ = 0 := by rw [h, sub_self]
  apply mul_eq_zero.mp at h'
  rcases h' with h0 | h1
  · left
    exact sub_eq_zero.mp h0
  · right
    apply sub_eq_zero.mp
    simpa using h1

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · by_cases h'' : Q
      · right; exact h''
      · apply h at h'
        contradiction
    · left; exact h'
  · intro h h'
    rcases h with h0 | h1
    · contradiction
    · exact h1
