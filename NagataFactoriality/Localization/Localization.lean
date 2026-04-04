import NagataFactoriality.Localization.MultSet

namespace NagataFactoriality

structure Fraction {α : Type _} [CommRing α] [IsDomain α] (S : MultSet α) where
  num : α
  den : α
  den_mem : S den

namespace Fraction

variable {α : Type _} [CommRing α] [IsDomain α] {S : MultSet α}

def Rel (x y : Fraction S) : Prop := x.num * y.den = y.num * x.den

def zero : Fraction S := ⟨0, 1, S.one_mem⟩

def one : Fraction S := ⟨1, 1, S.one_mem⟩

def add (x y : Fraction S) : Fraction S :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, S.mul_mem x.den_mem y.den_mem⟩

def neg (x : Fraction S) : Fraction S :=
  ⟨-x.num, x.den, x.den_mem⟩

def mul (x y : Fraction S) : Fraction S :=
  ⟨x.num * y.num, x.den * y.den, S.mul_mem x.den_mem y.den_mem⟩

theorem rel_refl (x : Fraction S) : Rel x x := by
  rfl

theorem rel_symm {x y : Fraction S} : Rel x y → Rel y x := by
  intro h
  exact h.symm

theorem rel_trans {x y z : Fraction S} : Rel x y → Rel y z → Rel x z := by
  intro hxy hyz
  apply _root_.mul_left_cancel₀ (MultSet.ne_zero y.den_mem)
  grind [Rel]

theorem rel_add {x x' y y' : Fraction S} (hx : Rel x x') (hy : Rel y y') :
    Rel (add x y) (add x' y') := by
  unfold Rel add at *
  grind

theorem rel_neg {x y : Fraction S} (h : Rel x y) : Rel (neg x) (neg y) := by
  have hneg : -(x.num * y.den) = -(y.num * x.den) := congrArg (fun t => -t) h
  calc
    (-x.num) * y.den = -(x.num * y.den) := by grind
    _ = -(y.num * x.den) := hneg
    _ = (-y.num) * x.den := by grind

theorem rel_mul {x x' y y' : Fraction S} (hx : Rel x x') (hy : Rel y y') :
    Rel (mul x y) (mul x' y') := by
  unfold Rel mul at *
  grind

theorem add_assoc (x y z : Fraction S) : Rel (add (add x y) z) (add x (add y z)) := by
  unfold Rel add
  grind

theorem add_comm (x y : Fraction S) : Rel (add x y) (add y x) := by
  unfold Rel add
  grind

theorem add_zero (x : Fraction S) : Rel (add x zero) x := by
  unfold Rel add zero
  grind

theorem zero_add (x : Fraction S) : Rel (add zero x) x := by
  unfold Rel add zero
  grind

theorem neg_add_cancel (x : Fraction S) : Rel (add (neg x) x) zero := by
  unfold Rel add neg zero
  grind

theorem mul_assoc (x y z : Fraction S) : Rel (mul (mul x y) z) (mul x (mul y z)) := by
  unfold Rel mul
  grind

theorem mul_comm (x y : Fraction S) : Rel (mul x y) (mul y x) := by
  unfold Rel mul
  grind

theorem mul_one (x : Fraction S) : Rel (mul x one) x := by
  unfold Rel mul one
  grind

theorem one_mul (x : Fraction S) : Rel (mul one x) x := by
  unfold Rel mul one
  grind

theorem left_distrib (x y z : Fraction S) :
    Rel (mul x (add y z)) (add (mul x y) (mul x z)) := by
  unfold Rel mul add
  grind

theorem right_distrib (x y z : Fraction S) :
    Rel (mul (add x y) z) (add (mul x z) (mul y z)) := by
  unfold Rel mul add
  grind

theorem zero_mul (x : Fraction S) : Rel (mul zero x) zero := by
  unfold Rel mul zero
  grind

theorem mul_zero (x : Fraction S) : Rel (mul x zero) zero := by
  unfold Rel mul zero
  grind

def relSetoid (S : MultSet α) : Setoid (Fraction S) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

end Fraction

abbrev Localization {α : Type _} [CommRing α] [IsDomain α] (S : MultSet α) :=
  Quotient (Fraction.relSetoid S)

namespace Localization

variable {α : Type _} [CommRing α] [IsDomain α] {S : MultSet α}

def mk (a s : α) (hs : S s) : Localization S :=
  Quotient.mk (Fraction.relSetoid S) ⟨a, s, hs⟩

def of (a : α) : Localization S :=
  mk (S := S) a 1 S.one_mem

instance : Zero (Localization S) := ⟨Quotient.mk (Fraction.relSetoid S) Fraction.zero⟩

instance : One (Localization S) := ⟨Quotient.mk (Fraction.relSetoid S) Fraction.one⟩

instance : Add (Localization S) where
  add x y :=
    Quotient.liftOn₂ x y
      (fun a b => Quotient.mk (Fraction.relSetoid S) (Fraction.add a b))
      (by
        intro a b a' b' ha hb
        exact Quotient.sound (Fraction.rel_add ha hb))

instance : Neg (Localization S) where
  neg x :=
    Quotient.liftOn x
      (fun a => Quotient.mk (Fraction.relSetoid S) (Fraction.neg a))
      (by
        intro a b hab
        exact Quotient.sound (Fraction.rel_neg hab))

instance : Mul (Localization S) where
  mul x y :=
    Quotient.liftOn₂ x y
      (fun a b => Quotient.mk (Fraction.relSetoid S) (Fraction.mul a b))
      (by
        intro a b a' b' ha hb
        exact Quotient.sound (Fraction.rel_mul ha hb))

instance : Sub (Localization S) := ⟨fun x y => x + -y⟩

@[simp] theorem mk_eq (a s : α) (hs : S s) :
    Quotient.mk (Fraction.relSetoid S) ⟨a, s, hs⟩ = mk (S := S) a s hs := rfl

@[simp] theorem of_zero : of (S := S) (0 : α) = (Zero.zero : Localization S) := by
  rfl

@[simp] theorem of_one : of (S := S) (1 : α) = (One.one : Localization S) := by
  rfl

@[simp] theorem of_add (a b : α) : of (S := S) (a + b) = of a + of b := by
  apply Quotient.sound
  show (a + b) * (1 * 1) = (a * 1 + b * 1) * 1
  grind

@[simp] theorem of_mul (a b : α) : of (S := S) (a * b) = of a * of b := by
  apply Quotient.sound
  show (a * b) * (1 * 1) = (a * b) * 1
  grind

@[simp] theorem of_neg (a : α) : of (S := S) (-a) = -of a := by
  apply Quotient.sound
  show (-a) * 1 = (-a) * 1
  grind

instance : AddCommGroup (Localization S) where
  add := (· + ·)
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    exact Quotient.sound (Fraction.add_assoc a b c)
  zero := 0
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.zero_add a)
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.add_zero a)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := @nsmulRec _ ⟨(0 : Localization S)⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec _ ⟨(0 : Localization S)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
    (@nsmulRec _ ⟨(0 : Localization S)⟩ ⟨(· + ·)⟩)
  neg_add_cancel := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.neg_add_cancel a)
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact Quotient.sound (Fraction.add_comm a b)

instance : AddCommGroupWithOne (Localization S) where
  __ := inferInstanceAs (AddCommGroup (Localization S))
  one := 1
  natCast := fun n => Nat.rec (0 : Localization S) (fun _ z => z + 1) n
  natCast_zero := rfl
  natCast_succ := by
    intro n
    rfl

instance : CommMonoidWithZero (Localization S) where
  mul := (· * ·)
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    exact Quotient.sound (Fraction.mul_assoc a b c)
  one := 1
  one_mul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.one_mul a)
  mul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.mul_one a)
  npow := @npowRec _ ⟨(1 : Localization S)⟩ ⟨(· * ·)⟩
  zero := 0
  zero_mul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.zero_mul a)
  mul_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Fraction.mul_zero a)
  mul_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact Quotient.sound (Fraction.mul_comm a b)

instance : CommRing (Localization S) where
  __ := inferInstanceAs (AddCommGroupWithOne (Localization S))
  __ := inferInstanceAs (CommMonoidWithZero (Localization S))
  left_distrib := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    exact Quotient.sound (Fraction.left_distrib a b c)
  right_distrib := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    exact Quotient.sound (Fraction.right_distrib a b c)

instance : Nontrivial (Localization S) where
  exists_pair_ne := ⟨0, 1, by
    intro h
    have h' : Fraction.Rel Fraction.zero Fraction.one := Quotient.exact h
    have h01 : (0 : α) = 1 := by
      unfold Fraction.Rel Fraction.zero Fraction.one at h'
      grind
    exact zero_ne_one h01⟩

theorem mul_eq_zero {x y : Localization S} (hab : x * y = 0) : x = 0 ∨ y = 0 := by
  refine Quotient.inductionOn₂ x y ?_ hab
  intro a b hab
  have hab' : a.num * b.num = 0 := by
    have hrel : Fraction.Rel (Fraction.mul a b) Fraction.zero := Quotient.exact hab
    unfold Fraction.Rel Fraction.mul Fraction.zero at hrel
    have h0 : a.num * b.num * 1 = 0 := by
      calc
        a.num * b.num * 1 = 0 * (a.den * b.den) := hrel
        _ = 0 := by grind
    grind
  rcases _root_.mul_eq_zero.mp hab' with ha0 | hb0
  · left
    apply Quotient.sound
    show a.num * 1 = 0 * a.den
    grind
  · right
    apply Quotient.sound
    show b.num * 1 = 0 * b.den
    grind

instance : NoZeroDivisors (Localization S) := ⟨fun {x y} => mul_eq_zero (S := S) (x := x) (y := y)⟩

instance : IsDomain (Localization S) := NoZeroDivisors.to_isDomain _

end Localization

end NagataFactoriality
