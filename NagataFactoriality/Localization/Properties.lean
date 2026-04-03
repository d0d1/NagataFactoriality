import NagataFactoriality.Localization.Localization

open Lean.Grind

namespace NagataFactoriality

namespace Localization

variable {α : Type _} [IntegralDomain α] {S : MultSet α}

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

end Localization

end NagataFactoriality
