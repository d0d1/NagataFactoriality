import NagataFactoriality.Basic.Divisibility

open Lean.Grind

namespace NagataFactoriality

structure Ideal (α : Type _) [CommRing α] where
  carrier : α → Prop
  zero_mem : carrier 0
  add_mem : ∀ {a b : α}, carrier a → carrier b → carrier (a + b)
  mul_mem : ∀ r : α, ∀ {a : α}, carrier a → carrier (r * a)

namespace Ideal

variable {α : Type _} [CommRing α]

def Subset (I J : Ideal α) : Prop := ∀ ⦃a : α⦄, I.carrier a → J.carrier a

instance : LE (Ideal α) := ⟨Subset⟩

theorem le_refl (I : Ideal α) : I ≤ I := by
  intro a ha
  exact ha

theorem le_trans {I J K : Ideal α} : I ≤ J → J ≤ K → I ≤ K := by
  intro hIJ hJK a ha
  exact hJK (hIJ ha)

def principal [IntegralDomain α] (a : α) : Ideal α where
  carrier x := dvd a x
  zero_mem := by
    refine ⟨0, ?_⟩
    grind
  add_mem := by
    intro x y hx hy
    rcases hx with ⟨u, hu⟩
    rcases hy with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    grind
  mul_mem := by
    intro r x hx
    rcases hx with ⟨u, hu⟩
    refine ⟨r * u, ?_⟩
    grind

@[simp] theorem mem_principal [IntegralDomain α] {a x : α} :
    (principal a).carrier x ↔ dvd a x := Iff.rfl

end Ideal

def AscendingChain {α : Type _} [CommRing α] (c : Nat → Ideal α) : Prop :=
  ∀ n : Nat, c n ≤ c (n + 1)

def Stabilizes {α : Type _} [CommRing α] (c : Nat → Ideal α) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → c n = c N

def NoetherianRing (α : Type _) [CommRing α] : Prop :=
  ∀ c : Nat → Ideal α, AscendingChain c → Stabilizes c

end NagataFactoriality
