import NagataFactoriality.Localization.Properties
import NagataFactoriality.Basic.UFD

namespace NagataFactoriality

def Avoids {α : Type*} [CommRing α] [IsDomain α] (S : Submonoid α) (p : α) : Prop :=
  ∀ s : α, s ∈ S → ¬ p ∣ s

private def submonoidZeroNotMemFact {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : Fact ((0 : α) ∉ S) :=
  ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩

theorem prime_of_irreducible_of_dvd_mem {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p s : α}
    (hp : Irreducible p) (hs : s ∈ S) (hdiv : p ∣ s) : Prime p := by
  rcases hS s hs with hsPrime | hsUnit
  · have hsIrred : Irreducible s := prime_irreducible hsPrime
    have hassoc : Associated p s := associated_of_irreducible_of_dvd hp hsIrred hdiv
    exact prime_of_associated hsPrime (associated_symm hassoc)
  · exact False.elim (hp.not_isUnit (isUnit_of_dvd_unit hdiv hsUnit))

theorem localization_irreducible_of_irreducible {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by
  letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdiv : Localization.of (S := S) p ∣ (1 : Localization S) := by
      rcases isUnit_iff_exists_inv.mp hunit with ⟨x, hx⟩
      exact ⟨x, hx.symm⟩
    have hdiv' : Localization.of (S := S) p ∣ Localization.of (S := S) (1 : α) := by
      simpa using hdiv
    rcases (Localization.dvd_of_iff (S := S) (a := p) (b := 1)).1 hdiv' with ⟨s, hs, hps⟩
    exact havoid s hs (by simpa using hps)
  · intro x y hxy
    obtain ⟨a, s, hs, rfl⟩ := Localization.surj (S := S) x
    obtain ⟨b, t, ht, rfl⟩ := Localization.surj (S := S) y
    have hprod : p * (s * t) = a * b := by
      have hEq :
          Localization.of (S := S) p =
            Localization.mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by
        simpa [Localization.mk_mul_mk] using hxy
      have hEq' :
          Localization.mk (S := S) p 1 S.one_mem =
            Localization.mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by
        simpa [Localization.of] using hEq
      simpa [mul_one] using
        (Localization.mk_eq_iff (S := S) (hs := S.one_mem) (ht := S.mul_mem hs ht)).1 hEq'
    rcases hS (s * t) (S.mul_mem hs ht) with hstPrime | hstUnit
    · have hstdiv : s * t ∣ a * b := ⟨p, by simpa [hprod, mul_assoc, mul_left_comm, mul_comm]⟩
      rcases hstPrime.2.2 a b hstdiv with hdiva | hdivb
      · rcases hdiva with ⟨d, hd⟩
        have hst0 : s * t ≠ 0 := hstPrime.ne_zero
        have hp_eq : p = d * b := by
          apply mul_left_cancel₀ hst0
          calc
            (s * t) * p = p * (s * t) := by ac_rfl
            _ = a * b := hprod
            _ = ((s * t) * d) * b := by rw [hd]
            _ = (s * t) * (d * b) := by ac_rfl
        rcases hp.isUnit_or_isUnit hp_eq with hdUnit | hbUnit
        · left
          have hx_eq : Localization.mk (S := S) a s hs = Localization.of (S := S) (t * d) := by
            apply (Localization.mk_eq_iff (S := S) (hs := hs) (ht := S.one_mem)).2
            simpa [hd, mul_assoc, mul_left_comm, mul_comm]
          rw [hx_eq]
          have htUnitLoc : IsUnit (Localization.of (S := S) t) :=
            Localization.isUnit_of_mem (S := S) ht
          have hdUnitLoc : IsUnit (Localization.of (S := S) d) :=
            Localization.isUnit_of_isUnit (S := S) hdUnit
          simpa [Localization.of_mul] using isUnit_mul htUnitLoc hdUnitLoc
        · right
          exact Localization.isUnit_mk_of_isUnit (S := S) hbUnit ht
      · rcases hdivb with ⟨d, hd⟩
        have hst0 : s * t ≠ 0 := hstPrime.ne_zero
        have hp_eq : p = a * d := by
          apply mul_left_cancel₀ hst0
          calc
            (s * t) * p = p * (s * t) := by ac_rfl
            _ = a * b := hprod
            _ = a * ((s * t) * d) := by rw [hd]
            _ = (s * t) * (a * d) := by ac_rfl
        rcases hp.isUnit_or_isUnit hp_eq with haUnit | hdUnit
        · left
          exact Localization.isUnit_mk_of_isUnit (S := S) haUnit hs
        · right
          have hy_eq : Localization.mk (S := S) b t ht = Localization.of (S := S) (s * d) := by
            apply (Localization.mk_eq_iff (S := S) (hs := ht) (ht := S.one_mem)).2
            simpa [hd, mul_assoc, mul_left_comm, mul_comm]
          rw [hy_eq]
          have hsUnitLoc : IsUnit (Localization.of (S := S) s) :=
            Localization.isUnit_of_mem (S := S) hs
          have hdUnitLoc : IsUnit (Localization.of (S := S) d) :=
            Localization.isUnit_of_isUnit (S := S) hdUnit
          simpa [Localization.of_mul] using isUnit_mul hsUnitLoc hdUnitLoc
    · have hassoc : Associated p (a * b) := by
        simpa [hprod] using associated_mul_unit_right p (s * t) hstUnit
      have habIrred : Irreducible (a * b) := hassoc.irreducible hp
      exact (habIrred.isUnit_or_isUnit rfl).elim
        (fun haUnit => Or.inl (Localization.isUnit_mk_of_isUnit (S := S) haUnit hs))
        (fun hbUnit => Or.inr (Localization.isUnit_mk_of_isUnit (S := S) hbUnit ht))

theorem dvd_of_localization_dvd {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p a : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hdiv : Localization.of (S := S) p ∣ Localization.of (S := S) a) : p ∣ a := by
  letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  rcases (Localization.dvd_of_iff (S := S) (a := p) (b := a)).1 hdiv with ⟨s, hs, hsa⟩
  rcases hsa with ⟨c, hc⟩
  rcases hS s hs with hsPrime | hsUnit
  · have hsdiv : s ∣ p * c := ⟨a, hc.symm⟩
    rcases hsPrime.2.2 p c hsdiv with hsp | hsc
    · have hsIrred : Irreducible s := prime_irreducible hsPrime
      have hassoc : Associated s p := associated_of_irreducible_of_dvd hsIrred hp hsp
      exact False.elim (havoid s hs (dvd_of_associated (associated_symm hassoc)))
    · rcases hsc with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      have hs0 : s ≠ 0 := hsPrime.ne_zero
      have hcancel : s * a = s * (p * d) := by
        calc
          s * a = p * c := hc
          _ = p * (s * d) := by rw [hd]
          _ = s * (p * d) := by ac_rfl
      exact mul_left_cancel₀ hs0 hcancel
  · rcases hsUnit with ⟨u, rfl⟩
    refine ⟨(↑u⁻¹ : α) * c, ?_⟩
    calc
      a = (↑u⁻¹ : α) * ((u : α) * a) := by simp [mul_assoc]
      _ = (↑u⁻¹ : α) * (p * c) := by rw [hc]
      _ = p * ((↑u⁻¹ : α) * c) := by ac_rfl

theorem prime_of_localization_prime {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hploc : Prime (Localization.of (S := S) p)) : Prime p := by
  letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  refine ⟨hp.ne_zero, hp.not_isUnit, ?_⟩
  intro a b hdiv
  have hlocdiv : Localization.of (S := S) p ∣ Localization.of (S := S) (a * b) := by
    rcases hdiv with ⟨c, hc⟩
    exact ⟨Localization.of (S := S) c, by simpa [hc, Localization.of_mul]⟩
  rcases hploc.2.2 (Localization.of (S := S) a) (Localization.of (S := S) b)
      (by simpa [Localization.of_mul] using hlocdiv) with hpa | hpb
  · left
    exact dvd_of_localization_dvd hS hp havoid hpa
  · right
    exact dvd_of_localization_dvd hS hp havoid hpb

theorem nagata_key_lemma {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
          infer_instance))
    {p : α} (hp : Irreducible p) : Prime p := by
  letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  by_cases hmem : ∃ s : α, s ∈ S ∧ p ∣ s
  · rcases hmem with ⟨s, hs, hdiv⟩
    exact prime_of_irreducible_of_dvd_mem hS hp hs hdiv
  · have havoid : Avoids S p := by
      intro s hs hdiv
      exact hmem ⟨s, hs, hdiv⟩
    have hlocIrred : Irreducible (Localization.of (S := S) p) :=
      localization_irreducible_of_irreducible hS hp havoid
    letI : UniqueFactorizationMonoid (Localization S) := hUFD
    have hlocPrime : Prime (Localization.of (S := S) p) :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).mp hlocIrred
    exact prime_of_localization_prime hS hp havoid hlocPrime

end NagataFactoriality
