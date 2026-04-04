import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import NagataFactoriality.Basic.Divisibility

namespace NagataFactoriality

theorem hasFactorization_of_noetherian {α : Type*} [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : HasFactorization (α := α) := by
  exact (show WfDvdMonoid α from inferInstance)

theorem IsNoetherianRing.hasFactorization {α : Type*} [CommRing α] [IsDomain α]
    (h : IsNoetherianRing α) : HasFactorization (α := α) := by
  letI := h
  exact hasFactorization_of_noetherian (α := α)

end NagataFactoriality
