import NagataFactoriality.Basic.Divisibility

namespace NagataFactoriality

structure MultSet (α : Type _) [CommRing α] [IsDomain α] where
  carrier : α → Prop
  one_mem : carrier 1
  mul_mem : ∀ {a b : α}, carrier a → carrier b → carrier (a * b)
  zero_not_mem : ¬ carrier 0

namespace MultSet

variable {α : Type _} [CommRing α] [IsDomain α]

instance : CoeFun (MultSet α) (fun _ => α → Prop) := ⟨MultSet.carrier⟩

theorem ne_zero {S : MultSet α} {s : α} (hs : S s) : s ≠ 0 := by
  intro hs0
  exact S.zero_not_mem (by simpa [hs0] using hs)

inductive GeneratedBy (P : α → Prop) : α → Prop
  | one : GeneratedBy P 1
  | of {a : α} : P a → GeneratedBy P a
  | mul {a b : α} : GeneratedBy P a → GeneratedBy P b → GeneratedBy P (a * b)

theorem listProd_mem {S : MultSet α} {xs : List α} (hxs : ∀ x : α, x ∈ xs → S x) :
    S (listProd xs) := by
  induction xs with
  | nil =>
      simpa using S.one_mem
  | cons x xs ih =>
      simp at hxs
      exact S.mul_mem hxs.1 (ih hxs.2)

theorem generatedBy_mem {S : MultSet α} {P : α → Prop} {s : α}
    (hs : GeneratedBy (fun a => S a ∧ P a) s) : S s := by
  induction hs with
  | one =>
      exact S.one_mem
  | of h =>
      exact h.1
  | mul ha hb iha ihb =>
      exact S.mul_mem iha ihb

theorem generatedBy_to_list {P : α → Prop} {s : α} (hs : GeneratedBy P s) :
    ∃ factors : List α, listProd factors = s ∧ ∀ p : α, p ∈ factors → P p := by
  induction hs with
  | one =>
      refine ⟨[], by simp, ?_⟩
      intro p hp
      simp at hp
  | @of a h =>
      refine ⟨[a], by grind [listProd], ?_⟩
      intro p hp
      simp at hp
      simpa [hp] using h
  | mul ha hb iha ihb =>
      rcases iha with ⟨xs, hxs, hPx⟩
      rcases ihb with ⟨ys, hys, hPy⟩
      refine ⟨xs ++ ys, by simpa [hxs, hys, listProd_append], ?_⟩
      intro p hp
      rw [List.mem_append] at hp
      exact hp.elim (hPx p) (hPy p)

def GeneratedByPrimes (S : MultSet α) : Prop :=
  ∀ s : α, S s → GeneratedBy (fun a => S a ∧ Prime a) s

end MultSet

end NagataFactoriality
