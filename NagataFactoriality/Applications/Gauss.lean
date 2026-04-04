import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace NagataFactoriality

open Polynomial

theorem polynomial_content_mul {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    (p q : R[X]) : (p * q).content = p.content * q.content :=
  Polynomial.content_mul

theorem primitive_mul {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) : (p * q).IsPrimitive :=
  hp.mul hq

theorem polynomial_uniqueFactorizationMonoid {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[X] := by
  infer_instance

end NagataFactoriality
