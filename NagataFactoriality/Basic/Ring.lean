import Init.Grind.Ring.Basic

open Lean.Grind

namespace NagataFactoriality

class CommMonoid (α : Type _) extends One α, Mul α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a

attribute [instance 100] CommMonoid.toOne CommMonoid.toMul

namespace CommMonoid

variable {α : Type _} [CommMonoid α]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← CommMonoid.mul_assoc, CommMonoid.mul_comm a b, CommMonoid.mul_assoc]

end CommMonoid

abbrev AddCommGroup := Lean.Grind.AddCommGroup
abbrev Ring := Lean.Grind.Ring
abbrev CommRing := Lean.Grind.CommRing

instance instCommMonoidOfCommRing {α : Type _} [CommRing α] : CommMonoid α where
  one_mul := Semiring.one_mul
  mul_one := Semiring.mul_one
  mul_assoc := Semiring.mul_assoc
  mul_comm := CommSemiring.mul_comm

class IntegralDomain (α : Type _) extends CommRing α where
  zero_ne_one : (0 : α) ≠ 1
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : α}, a * b = 0 → a = 0 ∨ b = 0

namespace IntegralDomain

variable {α : Type _} [IntegralDomain α]

theorem one_ne_zero : (1 : α) ≠ 0 := by
  intro h
  exact IntegralDomain.zero_ne_one (by simpa using h.symm)

theorem mul_eq_zero {a b : α} : a * b = 0 → a = 0 ∨ b = 0 :=
  IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero

theorem mul_ne_zero {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero h with h0 | h0
  · exact ha h0
  · exact hb h0

theorem mul_right_cancel₀ {a b c : α} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hs : (a - b) * c = 0 := by
    grind
  rcases IntegralDomain.eq_zero_or_eq_zero_of_mul_eq_zero hs with hab | hc0
  · exact (AddCommGroup.sub_eq_zero_iff (a := a) (b := b)).mp hab
  · exact False.elim (hc hc0)

theorem mul_left_cancel₀ {a b c : α} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  apply IntegralDomain.mul_right_cancel₀ hc
  simpa [CommSemiring.mul_comm] using h

end IntegralDomain

end NagataFactoriality
