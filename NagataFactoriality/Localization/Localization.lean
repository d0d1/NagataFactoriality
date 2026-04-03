import NagataFactoriality.Localization.MultSet

open Lean.Grind

namespace NagataFactoriality

structure Fraction {α : Type _} [IntegralDomain α] (S : MultSet α) where
  num : α
  den : α
  den_mem : S den

namespace Fraction

variable {α : Type _} [IntegralDomain α] {S : MultSet α}

def Rel (x y : Fraction S) : Prop := x.num * y.den = y.num * x.den

theorem rel_refl (x : Fraction S) : Rel x x := by
  rfl

theorem rel_symm {x y : Fraction S} : Rel x y → Rel y x := by
  intro h
  exact h.symm

theorem rel_trans {x y z : Fraction S} : Rel x y → Rel y z → Rel x z := by
  intro hxy hyz
  apply IntegralDomain.mul_left_cancel₀ (MultSet.ne_zero y.den_mem)
  grind [Rel]

def relSetoid (S : MultSet α) : Setoid (Fraction S) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

end Fraction

abbrev Localization {α : Type _} [IntegralDomain α] (S : MultSet α) :=
  Quotient (Fraction.relSetoid S)

namespace Localization

variable {α : Type _} [IntegralDomain α] {S : MultSet α}

def mk (a s : α) (hs : S s) : Localization S :=
  Quotient.mk (Fraction.relSetoid S) ⟨a, s, hs⟩

def of (a : α) : Localization S :=
  mk (S := S) a 1 S.one_mem

end Localization

end NagataFactoriality
