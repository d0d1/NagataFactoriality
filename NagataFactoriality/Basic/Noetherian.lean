import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import NagataFactoriality.Basic.Divisibility

namespace NagataFactoriality

theorem hasFactorization_of_noetherian {α : Type*} [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : WfDvdMonoid α := by
  infer_instance

theorem IsNoetherianRing.hasFactorization {α : Type*} [CommRing α] [IsDomain α]
    (h : IsNoetherianRing α) : WfDvdMonoid α := by
  letI := h
  exact hasFactorization_of_noetherian (α := α)

end NagataFactoriality
