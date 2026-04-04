import NagataFactoriality.Localization.Properties
import NagataFactoriality.Basic.UFD

namespace NagataFactoriality

def Avoids {α : Type*} [CommRing α] [IsDomain α] (S : Submonoid α) (p : α) : Prop :=
  ∀ s : α, s ∈ S → ¬ p ∣ s

/-- A submonoid is prime-generated if each of its elements is a finite product of prime elements. -/
def PrimeGenerated {α : Type*} [CommRing α] (S : Submonoid α) : Prop :=
  ∀ s : α, s ∈ S → ∃ f : Multiset α, (∀ q ∈ f, q ∈ S ∧ Prime q) ∧ f.prod = s

private def submonoidZeroNotMemFact {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : Fact ((0 : α) ∉ S) :=
  ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩

theorem multiset_prod_ne_zero_of_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) : f.prod ≠ 0 := by
  revert hf
  refine Multiset.induction_on f ?_ ?_
  · intro _
    exact one_ne_zero
  · intro q qs ih hqs
    have hq : Prime q := hqs q (by simp)
    have htail : ∀ r ∈ qs, Prime r := by
      intro r hr
      exact hqs r (by simp [hr])
    simpa using mul_ne_zero hq.ne_zero (ih htail)

theorem zero_notMem_of_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S) : (0 : α) ∉ S := by
  intro hs
  rcases hS 0 hs with ⟨f, hf, hprod⟩
  exact (multiset_prod_ne_zero_of_prime_factors (fun q hq => (hf q hq).2)) hprod

theorem primeGenerated_powers {α : Type*} [CommRing α] {p : α} (hp : Prime p) :
    PrimeGenerated (Submonoid.powers p) := by
  intro s hs
  rcases hs with ⟨n, rfl⟩
  refine ⟨Multiset.replicate n p, ?_, by simp⟩
  intro q hq
  have hqp : q = p := by
    exact Multiset.eq_of_mem_replicate hq
  subst hqp
  refine ⟨⟨1, by simp⟩, hp⟩

theorem prime_of_irreducible_of_dvd_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p : α}
    (hp : Irreducible p) (hdiv : p ∣ f.prod) : Prime p := by
  revert hf hdiv
  refine Multiset.induction_on f ?_ ?_
  · intro _ hdiv
    exact False.elim (hp.not_isUnit (isUnit_of_dvd_one (by simpa using hdiv)))
  · intro q qs ih hqs hdiv
    have hq : Prime q := hqs q (by simp)
    have htail : ∀ r ∈ qs, Prime r := by
      intro r hr
      exact hqs r (by simp [hr])
    rcases hdiv with ⟨d, hd⟩
    have hq_dvd : q ∣ p * d := by
      refine ⟨qs.prod, ?_⟩
      simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hd.symm
    rcases hq.2.2 p d hq_dvd with hqp | hqd
    · have hqIrred : Irreducible q := prime_irreducible hq
      have hassoc : Associated q p := associated_of_irreducible_of_dvd hqIrred hp hqp
      exact prime_of_associated hq hassoc
    · rcases hqd with ⟨e, hde⟩
      have hcancel : qs.prod = p * e := by
        apply mul_left_cancel₀ hq.ne_zero
        calc
          q * qs.prod = p * d := by simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hd
          _ = p * (q * e) := by rw [hde]
          _ = q * (p * e) := by ac_rfl
      exact ih htail ⟨e, hcancel⟩

theorem prime_of_irreducible_of_dvd_mem_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p s : α}
    (hp : Irreducible p) (hs : s ∈ S) (hdiv : p ∣ s) : Prime p := by
  rcases hS s hs with ⟨f, hf, hprod⟩
  rw [← hprod] at hdiv
  exact prime_of_irreducible_of_dvd_prime_factors (fun q hq => (hf q hq).2) hp hdiv

theorem dvd_of_mul_eq_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a c : α} (hp : Irreducible p)
    (hnot : ∀ q ∈ f, ¬ p ∣ q) (hEq : f.prod * a = p * c) : p ∣ a := by
  have hmain :
      ∀ g : Multiset α, (∀ q ∈ g, Prime q) → (∀ q ∈ g, ¬ p ∣ q) →
        ∀ {d : α}, g.prod * a = p * d → p ∣ a := by
    intro g
    refine Multiset.induction_on g ?_ ?_
    · intro hg hnotg d hEqg
      refine ⟨d, ?_⟩
      simpa using hEqg
    · intro q qs ih hqs hnotqs d hEqqs
      have hq : Prime q := hqs q (by simp)
      have htail : ∀ r ∈ qs, Prime r := by
        intro r hr
        exact hqs r (by simp [hr])
      have htailNot : ∀ r ∈ qs, ¬ p ∣ r := by
        intro r hr
        exact hnotqs r (by simp [hr])
      have hqNot : ¬ p ∣ q := hnotqs q (by simp)
      have hq_dvd : q ∣ p * d := by
        refine ⟨qs.prod * a, ?_⟩
        simpa [mul_assoc] using hEqqs.symm
      rcases hq.2.2 p d hq_dvd with hqp | hqc
      · have hqIrred : Irreducible q := prime_irreducible hq
        have hassoc : Associated q p := associated_of_irreducible_of_dvd hqIrred hp hqp
        exact False.elim (hqNot (dvd_of_associated (associated_symm hassoc)))
      · rcases hqc with ⟨e, hd⟩
        have hq0 : q ≠ 0 := hq.ne_zero
        have hEq' : q * (qs.prod * a) = q * (p * e) := by
          calc
            q * (qs.prod * a) = (q ::ₘ qs).prod * a := by simp [mul_assoc]
            _ = p * d := hEqqs
            _ = p * (q * e) := by rw [hd]
            _ = q * (p * e) := by ac_rfl
        have hcancel : qs.prod * a = p * e := mul_left_cancel₀ hq0 hEq'
        exact ih htail htailNot hcancel
  exact hmain f hf hnot hEq

theorem dvd_of_localization_dvd_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S) {p a : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hdiv : Localization.of (S := S) p ∣ Localization.of (S := S) a) : p ∣ a := by
  letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  rcases (Localization.dvd_of_iff (S := S) (a := p) (b := a)).1 hdiv with ⟨s, hs, hsa⟩
  rcases hsa with ⟨c, hc⟩
  rcases hS s hs with ⟨f, hf, hprod⟩
  have hnot : ∀ q ∈ f, ¬ p ∣ q := by
    intro q hq hpq
    have hq_dvd_prod : q ∣ f.prod := Multiset.dvd_prod hq
    have hp_dvd_s : p ∣ s := by
      rw [← hprod]
      exact dvd_trans hpq hq_dvd_prod
    exact havoid s hs hp_dvd_s
  have hEq : f.prod * a = p * c := by
    simpa [hprod] using hc
  exact dvd_of_mul_eq_prime_factors (fun q hq => (hf q hq).2) hp hnot hEq

theorem multiset_prod_mem_of_factors {α : Type*} [CommMonoid α] {S : Submonoid α} {f : Multiset α}
    (hf : ∀ q ∈ f, q ∈ S) : f.prod ∈ S := by
  revert hf
  refine Multiset.induction_on f ?_ ?_
  · intro _
    simp
  · intro q qs ih hqs
    have hq : q ∈ S := hqs q (by simp)
    have htail : ∀ r ∈ qs, r ∈ S := by
      intro r hr
      exact hqs r (by simp [hr])
    simpa using S.mul_mem hq (ih htail)

theorem split_prime_factors_of_mul_eq {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a b : α} (_hp : Irreducible p)
    (hEq : p * f.prod = a * b) :
    ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
      f₁ + f₂ = f ∧
      a = f₁.prod * a' ∧
      b = f₂.prod * b' ∧
      p = a' * b' := by
  have hmain :
      ∀ (g : Multiset α) (a b : α), (∀ q ∈ g, Prime q) → p * g.prod = a * b →
        ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
          f₁ + f₂ = g ∧
          a = f₁.prod * a' ∧
          b = f₂.prod * b' ∧
          p = a' * b' := by
    intro g
    refine Multiset.induction_on g ?_ ?_
    · intro a b _ hEq
      refine ⟨0, 0, a, b, rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hEq
    · intro q qs ih a b hqs hEq
      have hq : Prime q := hqs q (by simp)
      have htail : ∀ r ∈ qs, Prime r := by
        intro r hr
        exact hqs r (by simp [hr])
      have hq_dvd_ab : q ∣ a * b := by
        refine ⟨p * qs.prod, ?_⟩
        calc
          a * b = p * (q * qs.prod) := by
            simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq.symm
          _ = q * (p * qs.prod) := by ac_rfl
      rcases hq.2.2 a b hq_dvd_ab with hqa | hqb
      · rcases hqa with ⟨a₁, ha₁⟩
        have hEq' : p * qs.prod = a₁ * b := by
          have haux : q * (p * qs.prod) = q * (a₁ * b) := by
            calc
              q * (p * qs.prod) = p * (q * qs.prod) := by ac_rfl
              _ = a * b := by
                simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq
              _ = (q * a₁) * b := by rw [ha₁]
              _ = q * (a₁ * b) := by ac_rfl
          exact mul_left_cancel₀ hq.ne_zero haux
        rcases ih (a := a₁) (b := b) htail hEq' with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
        refine ⟨q ::ₘ f₁, f₂, a', b', ?_, ?_, hb, hpab⟩
        · simp [hpart]
        · calc
            a = q * a₁ := ha₁
            _ = q * (f₁.prod * a') := by rw [ha]
            _ = (q ::ₘ f₁).prod * a' := by simp [mul_assoc]
      · rcases hqb with ⟨b₁, hb₁⟩
        have hEq' : p * qs.prod = a * b₁ := by
          have haux : q * (p * qs.prod) = q * (a * b₁) := by
            calc
              q * (p * qs.prod) = p * (q * qs.prod) := by ac_rfl
              _ = a * b := by
                simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq
              _ = a * (q * b₁) := by rw [hb₁]
              _ = q * (a * b₁) := by ac_rfl
          exact mul_left_cancel₀ hq.ne_zero haux
        rcases ih (a := a) (b := b₁) htail hEq' with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
        refine ⟨f₁, q ::ₘ f₂, a', b', ?_, ha, ?_, hpab⟩
        · simp [hpart]
        · calc
            b = q * b₁ := hb₁
            _ = q * (f₂.prod * b') := by rw [hb]
            _ = (q ::ₘ f₂).prod * b' := by simp [mul_assoc]
  exact hmain f a b hf hEq

theorem localization_irreducible_of_irreducible_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by
  letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
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
    have hEq :
        p * (s * t) = a * b := by
      have hloc :
          Localization.of (S := S) p =
            Localization.mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by
        simpa [Localization.mk_mul_mk] using hxy
      have hmk :
          Localization.mk (S := S) p 1 S.one_mem =
            Localization.mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by
        simpa [Localization.of] using hloc
      simpa [mul_one] using
        (Localization.mk_eq_iff (S := S) (hs := S.one_mem) (ht := S.mul_mem hs ht)).1 hmk
    rcases hS (s * t) (S.mul_mem hs ht) with ⟨f, hf, hfprod⟩
    rcases split_prime_factors_of_mul_eq (fun q hq => (hf q hq).2) hp (by simpa [hfprod] using hEq)
        with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
    rcases hp.isUnit_or_isUnit hpab with haUnit | hbUnit
    · left
      have hf₁mem : ∀ q ∈ f₁, q ∈ S := by
        intro q hq
        exact (hf q (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inl hq))).1
      have hprodMem : f₁.prod ∈ S := multiset_prod_mem_of_factors hf₁mem
      have hx_eq :
          Localization.mk (S := S) a s hs =
            Localization.of (S := S) f₁.prod * Localization.mk (S := S) a' s hs := by
        rw [ha]
        symm
        exact Localization.of_mul_mk (S := S) f₁.prod a' s hs
      rw [hx_eq]
      exact isUnit_mul (Localization.isUnit_of_mem (S := S) hprodMem)
        (Localization.isUnit_mk_of_isUnit (S := S) haUnit hs)
    · right
      have hf₂mem : ∀ q ∈ f₂, q ∈ S := by
        intro q hq
        exact (hf q (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inr hq))).1
      have hprodMem : f₂.prod ∈ S := multiset_prod_mem_of_factors hf₂mem
      have hy_eq :
          Localization.mk (S := S) b t ht =
            Localization.of (S := S) f₂.prod * Localization.mk (S := S) b' t ht := by
        rw [hb]
        symm
        exact Localization.of_mul_mk (S := S) f₂.prod b' t ht
      rw [hy_eq]
      exact isUnit_mul (Localization.isUnit_of_mem (S := S) hprodMem)
        (Localization.isUnit_mk_of_isUnit (S := S) hbUnit ht)

theorem prime_of_localization_prime_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S) {p : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hploc : Prime (Localization.of (S := S) p)) : Prime p := by
  letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  refine ⟨hp.ne_zero, hp.not_isUnit, ?_⟩
  intro a b hdiv
  have hlocdiv : Localization.of (S := S) p ∣ Localization.of (S := S) (a * b) := by
    rcases hdiv with ⟨c, hc⟩
    exact ⟨Localization.of (S := S) c, by simp [hc, Localization.of_mul]⟩
  rcases hploc.2.2 (Localization.of (S := S) a) (Localization.of (S := S) b)
      (by simpa [Localization.of_mul] using hlocdiv) with hpa | hpb
  · left
    exact dvd_of_localization_dvd_primeGenerated hS hp havoid hpa
  · right
    exact dvd_of_localization_dvd_primeGenerated hS hp havoid hpb

theorem nagata_key_lemma_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance))
    {p : α} (hp : Irreducible p) : Prime p := by
  letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  by_cases hmem : ∃ s : α, s ∈ S ∧ p ∣ s
  · rcases hmem with ⟨s, hs, hdiv⟩
    exact prime_of_irreducible_of_dvd_mem_primeGenerated hS hp hs hdiv
  · have havoid : Avoids S p := by
      intro s hs hdiv
      exact hmem ⟨s, hs, hdiv⟩
    have hlocIrred : Irreducible (Localization.of (S := S) p) :=
      localization_irreducible_of_irreducible_primeGenerated hS hp havoid
    letI : UniqueFactorizationMonoid (Localization S) := hUFD
    have hlocPrime : Prime (Localization.of (S := S) p) :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).mp hlocIrred
    exact prime_of_localization_prime_primeGenerated hS hp havoid hlocPrime

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
    · have hstdiv : s * t ∣ a * b := by
        refine ⟨p, ?_⟩
        calc
          a * b = p * (s * t) := hprod.symm
          _ = (s * t) * p := by ac_rfl
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
            calc
              a * 1 = a := by simp
              _ = s * t * d := by rw [hd]
              _ = (t * d) * s := by ac_rfl
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
            calc
              b * 1 = b := by simp
              _ = s * t * d := by rw [hd]
              _ = (s * d) * t := by ac_rfl
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
      a = (↑u⁻¹ : α) * ((u : α) * a) := by simp
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
    exact ⟨Localization.of (S := S) c, by simp [hc, Localization.of_mul]⟩
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
