import NagataFactoriality.Basic.Divisibility

namespace NagataFactoriality

structure MultSet (α : Type _) [IntegralDomain α] where
  carrier : α → Prop
  one_mem : carrier 1
  mul_mem : ∀ {a b : α}, carrier a → carrier b → carrier (a * b)
  zero_not_mem : ¬ carrier 0

namespace MultSet

variable {α : Type _} [IntegralDomain α]

instance : CoeFun (MultSet α) (fun _ => α → Prop) := ⟨MultSet.carrier⟩

theorem ne_zero {S : MultSet α} {s : α} (hs : S s) : s ≠ 0 := by
  intro hs0
  exact S.zero_not_mem (by simpa [hs0] using hs)

inductive GeneratedBy (P : α → Prop) : α → Prop
  | one : GeneratedBy P 1
  | of {a : α} : P a → GeneratedBy P a
  | mul {a b : α} : GeneratedBy P a → GeneratedBy P b → GeneratedBy P (a * b)

end MultSet

end NagataFactoriality
