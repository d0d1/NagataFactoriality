import NagataFactoriality.Localization.Localization

open Lean.Grind

namespace NagataFactoriality

namespace Localization

variable {α : Type _} [IntegralDomain α] {S : MultSet α}

def φ : RingHom α (Localization S) where
  toFun := of (S := S)
  map_zero' := of_zero (S := S)
  map_one' := of_one (S := S)
  map_add' := of_add (S := S)
  map_mul' := of_mul (S := S)

@[simp] theorem φ_apply (a : α) : φ (S := S) a = of (S := S) a := rfl

@[simp] theorem φ_zero : φ (S := S) (0 : α) = 0 := by
  exact RingHom.map_zero (φ (S := S))

@[simp] theorem φ_one : φ (S := S) (1 : α) = 1 := by
  exact RingHom.map_one (φ (S := S))

@[simp] theorem φ_add (a b : α) : φ (S := S) (a + b) = φ (S := S) a + φ (S := S) b := by
  exact RingHom.map_add (φ (S := S)) a b

@[simp] theorem φ_mul (a b : α) : φ (S := S) (a * b) = φ (S := S) a * φ (S := S) b := by
  exact RingHom.map_mul (φ (S := S)) a b

theorem mk_eq_iff {a b s t : α} (hs : S s) (ht : S t) :
    mk (S := S) a s hs = mk (S := S) b t ht ↔ a * t = b * s := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem of_eq_iff (a b : α) :
    of (S := S) a = of (S := S) b ↔ a = b := by
  change mk (S := S) a 1 S.one_mem = mk (S := S) b 1 S.one_mem ↔ a = b
  rw [mk_eq_iff (S := S) (hs := S.one_mem) (ht := S.one_mem)]
  constructor
  · intro h
    grind
  · intro h
    grind

theorem mk_eq_zero_iff {a s : α} (hs : S s) :
    mk (S := S) a s hs = 0 ↔ a = 0 := by
  change mk (S := S) a s hs = mk (S := S) 0 1 S.one_mem ↔ a = 0
  rw [mk_eq_iff (S := S) (hs := hs) (ht := S.one_mem)]
  constructor
  · intro h
    grind
  · intro h
    grind

@[simp] theorem of_eq_zero_iff (a : α) :
    of (S := S) a = 0 ↔ a = 0 := by
  simpa [of] using mk_eq_zero_iff (S := S) (a := a) (s := 1) (hs := S.one_mem)

@[simp] theorem mk_mul_mk {a b s t : α} (hs : S s) (ht : S t) :
    mk (S := S) a s hs * mk (S := S) b t ht =
      mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := rfl

@[simp] theorem of_mul_mk (a b s : α) (hs : S s) :
    of (S := S) a * mk (S := S) b s hs = mk (S := S) (a * b) s hs := by
  change mk (S := S) (a * b) (1 * s) (S.mul_mem S.one_mem hs) =
    mk (S := S) (a * b) s hs
  exact (mk_eq_iff (S := S) (hs := S.mul_mem S.one_mem hs) (ht := hs)).2 (by
    grind)

@[simp] theorem mk_mul_of (a b s : α) (hs : S s) :
    mk (S := S) (a * b) s hs = mk (S := S) a s hs * of (S := S) b := by
  change mk (S := S) (a * b) s hs =
    mk (S := S) (a * b) (s * 1) (S.mul_mem hs S.one_mem)
  exact (mk_eq_iff (S := S) (hs := hs) (ht := S.mul_mem hs S.one_mem)).2 (by
    grind)

theorem isUnit_mk_of_mem {a s : α} (ha : S a) (hs : S s) :
    IsUnit (mk (S := S) a s hs) := by
  refine ⟨mk (S := S) s a ha, ?_⟩
  change mk (S := S) (a * s) (s * a) (S.mul_mem hs ha) = 1
  change mk (S := S) (a * s) (s * a) (S.mul_mem hs ha) = mk (S := S) 1 1 S.one_mem
  exact (mk_eq_iff (S := S) (hs := S.mul_mem hs ha) (ht := S.one_mem)).2 (by
    grind)

theorem isUnit_of_mem {s : α} (hs : S s) : IsUnit (of (S := S) s) := by
  simpa [of] using isUnit_mk_of_mem (S := S) (a := s) (s := 1) hs S.one_mem

theorem isUnit_of_isUnit {a : α} (ha : IsUnit a) : IsUnit (of (S := S) a) := by
  rcases ha with ⟨b, hb⟩
  refine ⟨of (S := S) b, ?_⟩
  calc
    of (S := S) a * of (S := S) b = of (S := S) (a * b) := by
      symm
      exact of_mul (S := S) a b
    _ = (One.one : Localization S) := by rw [hb, of_one]

theorem dvd_φ_iff {a b : α} :
    dvd (φ (S := S) a) (φ (S := S) b) ↔ ∃ s : α, S s ∧ dvd a (s * b) := by
  constructor
  · rintro ⟨x, hx⟩
    refine Quotient.inductionOn x ?_ hx
    intro c hxc
    refine ⟨c.den, c.den_mem, c.num, ?_⟩
    change Quotient.mk (Fraction.relSetoid S) ⟨b, 1, S.one_mem⟩ =
      Quotient.mk (Fraction.relSetoid S) (Fraction.mul ⟨a, 1, S.one_mem⟩ c) at hxc
    have hrel : Fraction.Rel ⟨b, 1, S.one_mem⟩ (Fraction.mul ⟨a, 1, S.one_mem⟩ c) :=
      Quotient.exact hxc
    calc
      c.den * b = b * c.den := by grind
      _ = a * c.num := by
        unfold Fraction.Rel Fraction.mul at hrel
        grind
  · rintro ⟨s, hs, c, hc⟩
    refine ⟨mk (S := S) c s hs, ?_⟩
    change mk (S := S) b 1 S.one_mem =
      mk (S := S) (a * c) (1 * s) (S.mul_mem S.one_mem hs)
    exact (mk_eq_iff (S := S) (hs := S.one_mem) (ht := S.mul_mem S.one_mem hs)).2 (by
      grind)

theorem dvd_of_iff {a b : α} :
    dvd (of (S := S) a) (of (S := S) b) ↔ ∃ s : α, S s ∧ dvd a (s * b) := by
  simpa using (dvd_φ_iff (S := S) (a := a) (b := b))

end Localization

end NagataFactoriality
