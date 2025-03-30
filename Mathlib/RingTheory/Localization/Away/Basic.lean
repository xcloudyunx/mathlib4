/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Localizations away from an element

## Main definitions

 * `IsLocalization.Away (x : R) S` expresses that `S` is a localization away from `x`, as an
   abbreviation of `IsLocalization (Submonoid.powers x) S`.
 * `exists_reduced_fraction' (hb : b ≠ 0)` produces a reduced fraction of the form `b = a * x^n` for
   some `n : ℤ` and some `a : R` that is not divisible by `x`.

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section Away

variable (x : R)

/-- Given `x : R`, the typeclass `IsLocalization.Away x S` states that `S` is
isomorphic to the localization of `R` at the submonoid generated by `x`.
See `IsLocalization.Away.mk` for a specialized constructor. -/
abbrev Away (S : Type*) [CommSemiring S] [Algebra R S] :=
  IsLocalization (Submonoid.powers x) S

namespace Away

variable [IsLocalization.Away x S]

/-- Given `x : R` and a localization map `F : R →+* S` away from `x`, `invSelf` is `(F x)⁻¹`. -/
noncomputable def invSelf : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩

@[simp]
theorem mul_invSelf : algebraMap R S x * invSelf x = 1 := by
  convert IsLocalization.mk'_mul_mk'_eq_one (M := Submonoid.powers x) (S := S) _ 1
  symm
  apply IsLocalization.mk'_one

/-- For `s : S` with `S` being the localization of `R` away from `x`,
this is a choice of `(r, n) : R × ℕ` such that `s * algebraMap R S (x ^ n) = algebraMap R S r`. -/
noncomputable def sec (s : S) : R × ℕ :=
  ⟨(IsLocalization.sec (Submonoid.powers x) s).1,
   (IsLocalization.sec (Submonoid.powers x) s).2.property.choose⟩

lemma sec_spec (s : S) : s * (algebraMap R S) (x ^ (IsLocalization.Away.sec x s).2) =
    algebraMap R S (IsLocalization.Away.sec x s).1 := by
  simp only [IsLocalization.Away.sec, ← IsLocalization.sec_spec]
  congr
  exact (IsLocalization.sec (Submonoid.powers x) s).2.property.choose_spec

lemma algebraMap_pow_isUnit (n : ℕ) : IsUnit (algebraMap R S x ^ n) :=
  IsUnit.pow _ <| IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

lemma algebraMap_isUnit : IsUnit (algebraMap R S x) :=
  IsLocalization.map_units _ (⟨x, 1, by simp⟩ : Submonoid.powers x)

lemma surj (z : S) : ∃ (n : ℕ) (a : R), z * algebraMap R S x ^ n = algebraMap R S a := by
  obtain ⟨⟨a, ⟨-, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers x) z
  use n, a
  simpa using h

lemma exists_of_eq {a b : R} (h : algebraMap R S a = algebraMap R S b) :
    ∃ (n : ℕ), x ^ n * a = x ^ n * b := by
  obtain ⟨⟨-, n, rfl⟩, hx⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers x) h
  use n

/-- Specialized constructor for `IsLocalization.Away`. -/
lemma mk (r : R) (map_unit : IsUnit (algebraMap R S r))
    (surj : ∀ s, ∃ (n : ℕ) (a : R), s * algebraMap R S r ^ n = algebraMap R S a)
    (exists_of_eq : ∀ a b, algebraMap R S a = algebraMap R S b → ∃ (n : ℕ), r ^ n * a = r ^ n * b) :
    IsLocalization.Away r S where
  map_units' := by
    rintro ⟨-, n, rfl⟩
    simp only [map_pow]
    exact IsUnit.pow _ map_unit
  surj' z := by
    obtain ⟨n, a, hn⟩ := surj z
    use ⟨a, ⟨r ^ n, n, rfl⟩⟩
    simpa using hn
  exists_of_eq {x y} h := by
    obtain ⟨n, hn⟩ := exists_of_eq x y h
    use ⟨r ^ n, n, rfl⟩

lemma of_associated {r r' : R} (h : Associated r r') [IsLocalization.Away r S] :
    IsLocalization.Away r' S := by
  obtain ⟨u, rfl⟩ := h
  refine mk _ ?_ (fun s ↦ ?_) (fun a b hab ↦ ?_)
  · simp [algebraMap_isUnit r, IsUnit.map _ u.isUnit]
  · obtain ⟨n, a, hn⟩ := surj r s
    use n, a * u ^ n
    simp [mul_pow, ← mul_assoc, hn]
  · obtain ⟨n, hn⟩ := exists_of_eq r hab
    use n
    rw [mul_pow, mul_comm (r ^ n), mul_assoc, mul_assoc, hn]

/-- If `r` and `r'` are associated elements of `R`, an `R`-algebra `S`
is the localization of `R` away from `r` if and only of it is the localization of `R` away from
`r'`. -/
lemma iff_of_associated {r r' : R} (h : Associated r r') :
    IsLocalization.Away r S ↔ IsLocalization.Away r' S :=
  ⟨fun _ ↦ IsLocalization.Away.of_associated h, fun _ ↦ IsLocalization.Away.of_associated h.symm⟩

lemma isUnit_of_dvd {r : R} (h : r ∣ x) : IsUnit (algebraMap R S r) :=
  isUnit_of_dvd_unit (map_dvd _ h) (algebraMap_isUnit x)

variable {g : R →+* P}

/-- Given `x : R`, a localization map `F : R →+* S` away from `x`, and a map of `CommSemiring`s
`g : R →+* P` such that `g x` is invertible, the homomorphism induced from `S` to `P` sending
`z : S` to `g y * (g x)⁻ⁿ`, where `y : R, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def lift (hg : IsUnit (g x)) : S →+* P :=
  IsLocalization.lift fun y : Submonoid.powers x =>
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.map (powMonoidHom n : P →* P) hg

@[simp]
theorem lift_eq (hg : IsUnit (g x)) (a : R) : lift x hg (algebraMap R S a) = g a :=
  IsLocalization.lift_eq _ _

@[simp]
theorem lift_comp (hg : IsUnit (g x)) : (lift x hg).comp (algebraMap R S) = g :=
  IsLocalization.lift_comp _

@[deprecated (since := "2024-11-25")] alias AwayMap.lift_eq := lift_eq
@[deprecated (since := "2024-11-25")] alias AwayMap.lift_comp := lift_comp

/-- Given `x y : R` and localizations `S`, `P` away from `x` and `y * x`
respectively, the homomorphism induced from `S` to `P`. -/
noncomputable def awayToAwayLeft (y : R) [Algebra R P] [IsLocalization.Away (y * x) P] : S →+* P :=
  lift x <| isUnit_of_dvd (y * x) (dvd_mul_left _ _)

/-- Given `x y : R` and localizations `S`, `P` away from `x` and `x * y`
respectively, the homomorphism induced from `S` to `P`. -/
noncomputable def awayToAwayRight (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] : S →+* P :=
  lift x <| isUnit_of_dvd (x * y) (dvd_mul_right _ _)

theorem awayToAwayLeft_eq (y : R) [Algebra R P] [IsLocalization.Away (y * x) P] (a : R) :
    awayToAwayLeft x y (algebraMap R S a) = algebraMap R P a :=
  lift_eq _ _ _

theorem awayToAwayRight_eq (y : R) [Algebra R P] [IsLocalization.Away (x * y) P] (a : R) :
    awayToAwayRight x y (algebraMap R S a) = algebraMap R P a :=
  lift_eq _ _ _

variable (S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable def map (f : R →+* P) (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (f r) Q] : S →+* Q :=
  IsLocalization.map Q f
    (show Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f by
      rintro x ⟨n, rfl⟩
      use n
      simp)

section Algebra

variable {A : Type*} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]
variable (Aₚ : Type*) [CommSemiring Aₚ] [Algebra A Aₚ] [Algebra R Aₚ] [IsScalarTower R A Aₚ]
variable (Bₚ : Type*) [CommSemiring Bₚ] [Algebra B Bₚ] [Algebra R Bₚ] [IsScalarTower R B Bₚ]

instance {f : A →+* B} (a : A) [Away (f a) Bₚ] : IsLocalization (.map f (.powers a)) Bₚ := by
  simpa

/-- Given a algebra map `f : A →ₐ[R] B` and an element `a : A`, we may construct a map
`Aₐ →ₐ[R] Bₐ`. -/
noncomputable def mapₐ (f : A →ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] : Aₚ →ₐ[R] Bₚ :=
  ⟨map Aₚ Bₚ f.toRingHom a, fun r ↦ by
    dsimp only [AlgHom.toRingHom_eq_coe, map, RingHom.coe_coe, OneHom.toFun_eq_coe]
    rw [IsScalarTower.algebraMap_apply R A Aₚ, IsScalarTower.algebraMap_eq R B Bₚ]
    simp⟩

@[simp]
lemma mapₐ_apply (f : A →ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] (x : Aₚ) :
    mapₐ Aₚ Bₚ f a x = map Aₚ Bₚ f.toRingHom a x :=
  rfl

variable {Aₚ} {Bₚ}

lemma mapₐ_injective_of_injective {f : A →ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
    (hf : Function.Injective f) : Function.Injective (mapₐ Aₚ Bₚ f a) :=
  IsLocalization.map_injective_of_injective _ _ _ hf

lemma mapₐ_surjective_of_surjective {f : A →ₐ[R] B} (a : A) [Away a Aₚ] [Away (f a) Bₚ]
    (hf : Function.Surjective f) : Function.Surjective (mapₐ Aₚ Bₚ f a) :=
  have : IsLocalization (Submonoid.map f.toRingHom (Submonoid.powers a)) Bₚ := by
    simp only [AlgHom.toRingHom_eq_coe, Submonoid.map_powers, RingHom.coe_coe]
    infer_instance
  IsLocalization.map_surjective_of_surjective _ _ _ hf

end Algebra

/-- Localizing the localization of `R` at `x` at the image of `y` is the same as localizing
`R` at `y * x`. See `IsLocalization.Away.mul'` for the `x * y` version. -/
lemma mul (T : Type*) [CommSemiring T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away (algebraMap R S y) T] :
    IsLocalization.Away (y * x) T := by
  refine mk _ ?_ (fun z ↦ ?_) (fun a b h ↦ ?_)
  · simp only [map_mul, IsUnit.mul_iff, IsScalarTower.algebraMap_apply R S T]
    exact ⟨algebraMap_isUnit _, IsUnit.map _ (algebraMap_isUnit x)⟩
  · obtain ⟨m, p, hpq⟩ := surj (algebraMap R S y) z
    obtain ⟨n, a, hab⟩ := surj x p
    use m + n, a * x ^ m * y ^ n
    simp only [mul_pow, pow_add, map_pow, map_mul, ← mul_assoc, hpq,
      IsScalarTower.algebraMap_apply R S T, ← hab]
    ring
  · repeat rw [IsScalarTower.algebraMap_apply R S T] at h
    obtain ⟨n, hn⟩ := exists_of_eq (algebraMap R S y) h
    simp only [← map_pow, ← map_mul, ← map_mul] at hn
    obtain ⟨m, hm⟩ := exists_of_eq x hn
    use n + m
    convert_to y ^ m * x ^ n * (x ^ m * (y ^ n * a)) = y ^ m * x ^ n * (x ^ m * (y ^ n * b))
    · ring
    · ring
    · rw [hm]

/-- Localizing the localization of `R` at `x` at the image of `y` is the same as localizing
`R` at `x * y`. See `IsLocalization.Away.mul` for the `y * x` version. -/
lemma mul' (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away (algebraMap R S y) T] :
    IsLocalization.Away (x * y) T :=
  mul_comm x y ▸ mul S T x y

/-- Localizing the localization of `R` at `x` at the image of `y` is the same as localizing
`R` at `y * x`. -/
instance (x y : R) [IsLocalization.Away x S] :
    IsLocalization.Away (y * x) (Localization.Away (algebraMap R S y)) :=
  IsLocalization.Away.mul S (Localization.Away (algebraMap R S y)) _ _

/-- Localizing the localization of `R` at `x` at the image of `y` is the same as localizing
`R` at `x * y`. -/
instance (x y : R) [IsLocalization.Away x S] :
    IsLocalization.Away (x * y) (Localization.Away (algebraMap R S y)) :=
  IsLocalization.Away.mul' S (Localization.Away (algebraMap R S y)) _ _

/-- If `S₁` is the localization of `R` away from `f` and `S₂` is the localization away from `g`,
then any localization `T` of `S₂` away from `f` is also a localization of `S₁` away from `g`. -/
lemma commutes {R : Type*} [CommSemiring R] (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (x y : R)
    [IsLocalization.Away x S₁] [IsLocalization.Away y S₂]
    [IsLocalization.Away (algebraMap R S₂ x) T] :
    IsLocalization.Away (algebraMap R S₁ y) T := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S₂ (Submonoid.powers x)) T := by
    simp only [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  convert IsLocalization.commutes S₁ S₂ T (Submonoid.powers x) (Submonoid.powers y)
  ext x
  simp [Algebra.algebraMapSubmonoid]

end Away

end Away

variable [IsLocalization M S]

section AtUnits

variable (R) (S)

/-- The localization away from a unit is isomorphic to the ring. -/
noncomputable def atUnit (x : R) (e : IsUnit x) [IsLocalization.Away x S] : R ≃ₐ[R] S :=
  atUnits R (Submonoid.powers x)
    (by rwa [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff])

/-- The localization at one is isomorphic to the ring. -/
noncomputable def atOne [IsLocalization.Away (1 : R) S] : R ≃ₐ[R] S :=
  @atUnit R _ S _ _ (1 : R) isUnit_one _

theorem away_of_isUnit_of_bijective {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] {r : R} (hr : IsUnit r) (H : Function.Bijective (algebraMap R S)) :
    IsLocalization.Away r S :=
  { map_units' := by
      rintro ⟨_, n, rfl⟩
      exact (algebraMap R S).isUnit_map (hr.pow _)
    surj' := fun z => by
      obtain ⟨z', rfl⟩ := H.2 z
      exact ⟨⟨z', 1⟩, by simp⟩
    exists_of_eq := fun {x y} => by
      rw [H.1.eq_iff]
      rintro rfl
      exact ⟨1, rfl⟩ }

end AtUnits

section Prod

lemma away_of_isIdempotentElem_of_mul {R S} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {e : R} (he : IsIdempotentElem e)
    (H : ∀ x y, algebraMap R S x = algebraMap R S y ↔ e * x = e * y)
    (H' : Function.Surjective (algebraMap R S)) :
    IsLocalization.Away e S where
  map_units' r := by
    obtain ⟨r, n, rfl⟩ := r
    simp [show algebraMap R S e = 1 by rw [← (algebraMap R S).map_one, H, mul_one, he]]
  surj' z := by
    obtain ⟨z, rfl⟩ := H' z
    exact ⟨⟨z, 1⟩, by simp⟩
  exists_of_eq {x y} h := ⟨⟨e, Submonoid.mem_powers e⟩, (H x y).mp h⟩

lemma away_of_isIdempotentElem {R S} [CommRing R] [CommRing S] [Algebra R S]
    {e : R} (he : IsIdempotentElem e)
    (H : RingHom.ker (algebraMap R S) = Ideal.span {1 - e})
    (H' : Function.Surjective (algebraMap R S)) :
    IsLocalization.Away e S :=
  away_of_isIdempotentElem_of_mul he (fun x y ↦ by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, H, ← he.ker_toSpanSingleton_eq_span,
      LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, sub_eq_zero]
    simp_rw [mul_comm e, smul_eq_mul]) H'

instance away_fst {R S} [CommSemiring R] [CommSemiring S] :
    letI := (RingHom.fst R S).toAlgebra
    IsLocalization.Away (R := R × S) (1, 0) R :=
  letI := (RingHom.fst R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ ↦ show xR = yR ↔ _ by simp) Prod.fst_surjective

instance away_snd {R S} [CommSemiring R] [CommSemiring S] :
    letI := (RingHom.snd R S).toAlgebra
    IsLocalization.Away (R := R × S) (0, 1) S :=
  letI := (RingHom.snd R S).toAlgebra
  away_of_isIdempotentElem_of_mul (by ext <;> simp)
    (fun ⟨xR, xS⟩ ⟨yR, yS⟩ ↦ show xS = yS ↔ _ by simp) Prod.snd_surjective

end Prod

end IsLocalization

namespace Localization

open IsLocalization

variable {M}

/-- Given a map `f : R →+* S` and an element `r : R`, such that `f r` is invertible,
  we may construct a map `Rᵣ →+* S`. -/
noncomputable abbrev awayLift (f : R →+* P) (r : R) (hr : IsUnit (f r)) :
    Localization.Away r →+* P :=
  IsLocalization.Away.lift r hr

lemma awayLift_mk {A : Type*} [CommRing A] (f : R →+* A) (r : R)
    (a : R) (v : A) (hv : f r * v = 1) (j : ℕ) :
    Localization.awayLift f r (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
      (Localization.mk a ⟨r ^ j, j, rfl⟩) = f a * v ^ j := by
  simp [Localization.mk_eq_mk', awayLift, Away.lift, IsLocalization.lift_mk',
    Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight, mul_assoc, ← mul_pow, (mul_comm _ _).trans hv]

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable abbrev awayMap (f : R →+* P) (r : R) :
    Localization.Away r →+* Localization.Away (f r) :=
  IsLocalization.Away.map _ _ f r

variable {A : Type*} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Given a map `f : A →ₐ[R] B` and an element `a : A`, we may construct a map `Aₐ →ₐ[R] Bₐ`. -/
noncomputable abbrev awayMapₐ (f : A →ₐ[R] B) (a : A) :
    Localization.Away a →ₐ[R] Localization.Away (f a) :=
  IsLocalization.Away.mapₐ _ _ f a

theorem algebraMap_injective_of_span_eq_top (s : Set R) (span_eq : Ideal.span s = ⊤) :
    Function.Injective (algebraMap R <| Π a : s, Away a.1) := fun x y eq ↦ by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (Ideal.eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalization.eq_iff_exists (.powers r.1) _).mp (congr_fun eq r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩

/-- The sheaf condition for the structure sheaf on `Spec R`
for a covering of the whole prime spectrum by basic opens. -/
theorem existsUnique_algebraMap_eq_of_span_eq_top (s : Set R) (span_eq : Ideal.span s = ⊤)
    (f : Π a : s, Away a.1) (h : ∀ a b : s,
      Away.awayToAwayRight (P := Away (a * b : R)) a.1 b (f a) = Away.awayToAwayLeft b.1 a (f b)) :
    ∃! r : R, ∀ a : s, algebraMap R _ r = f a := by
  have mem := (Ideal.eq_top_iff_one _).mp span_eq; clear span_eq
  wlog finset_eq : ∃ t : Finset R, t = s generalizing s
  · have ⟨t, hts, mem⟩ := Submodule.mem_span_finite_of_mem_span mem
    have ⟨r, eq, uniq⟩ := this t (fun a ↦ f ⟨a, hts a.2⟩)
      (fun a b ↦ h ⟨a, hts a.2⟩ ⟨b, hts b.2⟩) mem ⟨_, rfl⟩
    refine ⟨r, fun a ↦ ?_, fun _ eq ↦ uniq _ fun a ↦ eq ⟨a, hts a.2⟩⟩
    replace hts := Set.insert_subset a.2 hts
    classical
    have ⟨r', eq, _⟩ := this ({a.1} ∪ t) (fun a ↦ f ⟨a, hts a.2⟩) (fun a b ↦
      h ⟨a, hts a.2⟩ ⟨b, hts b.2⟩) (Ideal.span_mono (fun _ ↦ .inr) mem) ⟨{a.1} ∪ t, by simp⟩
    exact (congr_arg _ (uniq _ fun b ↦ eq ⟨b, .inr b.2⟩).symm).trans (eq ⟨a, .inl rfl⟩)
  have span_eq := (Ideal.eq_top_iff_one _).mpr mem
  refine existsUnique_of_exists_of_unique ?_ fun x y hx hy ↦
    algebraMap_injective_of_span_eq_top s span_eq (funext fun a ↦ (hx a).trans (hy a).symm)
  obtain ⟨s, rfl⟩ := finset_eq
  choose n r eq using fun a ↦ Away.surj a.1 (f a)
  let N := s.attach.sup n
  let r a := a ^ (N - n a) * r a
  have eq a : f a * algebraMap R _ (a ^ N) = algebraMap R _ (r a) := by
    rw [map_mul, ← eq, mul_left_comm, ← map_pow, ← map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup <| s.mem_attach a)]
  have eq2 a b : ∃ N', (a * b) ^ N' * (r a * b ^ N) = (a * b) ^ N' * (r b * a ^ N) :=
    Away.exists_of_eq (S := Away (a * b : R)) _ <| by
      simp_rw [map_mul, ← Away.awayToAwayRight_eq (S := Away a.1) a.1 b (r a),
        ← Away.awayToAwayLeft_eq (S := Away b.1) b.1 a (r b), ← eq, map_mul,
        Away.awayToAwayRight_eq, Away.awayToAwayLeft_eq, h, mul_assoc, ← map_mul, mul_comm]
  choose N' hN' using eq2
  let N' := (s ×ˢ s).attach.sup fun a ↦ N'
    ⟨_, (Finset.mem_product.mp a.2).1⟩ ⟨_, (Finset.mem_product.mp a.2).2⟩
  have eq2 a b : (a * b) ^ N' * (r a * b ^ N) = (a * b) ^ N' * (r b * a ^ N) := by
    dsimp only [N']; rw [← Nat.sub_add_cancel (Finset.le_sup <| (Finset.mem_attach _ ⟨⟨a, b⟩,
      Finset.mk_mem_product a.2 b.2⟩)), pow_add, mul_assoc, hN', ← mul_assoc]
  let N := N' + N
  let r a := a ^ N' * r a
  have eq a : f a * algebraMap R _ (a ^ N) = algebraMap R _ (r a) := by
    rw [map_mul, ← eq, mul_left_comm, ← map_mul, ← pow_add]
  have eq2 a b : r a * b ^ N = r b * a ^ N := by
    rw [pow_add, mul_mul_mul_comm, ← mul_pow, eq2,
      mul_comm a.1, mul_pow, mul_mul_mul_comm, ← pow_add]
  have ⟨c, eq1⟩ := (mem_span_range_iff_exists_fun _).mp <|
    (Ideal.eq_top_iff_one _).mp <| (Set.image_eq_range _ _ ▸ Ideal.span_pow_eq_top _ span_eq N)
  refine ⟨∑ b, c b * r b, fun a ↦ ((Away.algebraMap_isUnit a.1).pow N).mul_left_inj.mp ?_⟩
  simp_rw [← map_pow, eq, ← map_mul, Finset.sum_mul, mul_assoc, eq2 _ a, mul_left_comm (c _),
    ← Finset.mul_sum, ← smul_eq_mul (a := c _), eq1, mul_one]

end Localization

end CommSemiring

open Localization

variable {R : Type*} [CommSemiring R]

section NumDen

open IsLocalization

variable (x : R)
variable (B : Type*) [CommSemiring B] [Algebra R B] [IsLocalization.Away x B]

/-- `selfZPow x (m : ℤ)` is `x ^ m` as an element of the localization away from `x`. -/
noncomputable def selfZPow (m : ℤ) : B :=
  if _ : 0 ≤ m then algebraMap _ _ x ^ m.natAbs else mk' _ (1 : R) (Submonoid.pow x m.natAbs)

theorem selfZPow_of_nonneg {n : ℤ} (hn : 0 ≤ n) : selfZPow x B n = algebraMap R B x ^ n.natAbs :=
  dif_pos hn

@[simp]
theorem selfZPow_natCast (d : ℕ) : selfZPow x B d = algebraMap R B x ^ d :=
  selfZPow_of_nonneg _ _ (Int.natCast_nonneg d)

@[simp]
theorem selfZPow_zero : selfZPow x B 0 = 1 := by
  simp [selfZPow_of_nonneg _ _ le_rfl]

theorem selfZPow_of_neg {n : ℤ} (hn : n < 0) :
    selfZPow x B n = mk' _ (1 : R) (Submonoid.pow x n.natAbs) :=
  dif_neg hn.not_le

theorem selfZPow_of_nonpos {n : ℤ} (hn : n ≤ 0) :
    selfZPow x B n = mk' _ (1 : R) (Submonoid.pow x n.natAbs) := by
  by_cases hn0 : n = 0
  · simp [hn0, selfZPow_zero, Submonoid.pow_apply]
  · simp [selfZPow_of_neg _ _ (lt_of_le_of_ne hn hn0)]

@[simp]
theorem selfZPow_neg_natCast (d : ℕ) : selfZPow x B (-d) = mk' _ (1 : R) (Submonoid.pow x d) := by
  simp [selfZPow_of_nonpos _ _ (neg_nonpos.mpr (Int.natCast_nonneg d))]

@[simp]
theorem selfZPow_sub_natCast {n m : ℕ} :
    selfZPow x B (n - m) = mk' _ (x ^ n) (Submonoid.pow x m) := by
  by_cases h : m ≤ n
  · rw [IsLocalization.eq_mk'_iff_mul_eq, Submonoid.pow_apply, Subtype.coe_mk, ← Int.ofNat_sub h,
      selfZPow_natCast, ← map_pow, ← map_mul, ← pow_add, Nat.sub_add_cancel h]
  · rw [← neg_sub, ← Int.ofNat_sub (le_of_not_le h), selfZPow_neg_natCast,
      IsLocalization.mk'_eq_iff_eq]
    simp [Submonoid.pow_apply, ← pow_add, Nat.sub_add_cancel (le_of_not_le h)]

@[simp]
theorem selfZPow_add {n m : ℤ} : selfZPow x B (n + m) = selfZPow x B n * selfZPow x B m := by
  rcases le_or_lt 0 n with hn | hn <;> rcases le_or_lt 0 m with hm | hm
  · rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_nonneg _ _ hm,
      selfZPow_of_nonneg _ _ (add_nonneg hn hm), Int.natAbs_add_of_nonneg hn hm, pow_add]
  · have : n + m = n.natAbs - m.natAbs := by
      rw [Int.natAbs_of_nonneg hn, Int.ofNat_natAbs_of_nonpos hm.le, sub_neg_eq_add]
    rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_neg _ _ hm, this, selfZPow_sub_natCast,
      IsLocalization.mk'_eq_mul_mk'_one, map_pow]
  · have : n + m = m.natAbs - n.natAbs := by
      rw [Int.natAbs_of_nonneg hm, Int.ofNat_natAbs_of_nonpos hn.le, sub_neg_eq_add, add_comm]
    rw [selfZPow_of_nonneg _ _ hm, selfZPow_of_neg _ _ hn, this, selfZPow_sub_natCast,
      IsLocalization.mk'_eq_mul_mk'_one, map_pow, mul_comm]
  · rw [selfZPow_of_neg _ _ hn, selfZPow_of_neg _ _ hm, selfZPow_of_neg _ _ (add_neg hn hm),
      Int.natAbs_add_of_nonpos hn.le hm.le, ← mk'_mul, one_mul]
    congr
    ext
    simp [pow_add]

theorem selfZPow_mul_neg (d : ℤ) : selfZPow x B d * selfZPow x B (-d) = 1 := by
  by_cases hd : d ≤ 0
  · rw [selfZPow_of_nonpos x B hd, selfZPow_of_nonneg, ← map_pow, Int.natAbs_neg,
      Submonoid.pow_apply, IsLocalization.mk'_spec, map_one]
    apply nonneg_of_neg_nonpos
    rwa [neg_neg]
  · rw [selfZPow_of_nonneg x B (le_of_not_le hd), selfZPow_of_nonpos, ← map_pow, Int.natAbs_neg,
      Submonoid.pow_apply, IsLocalization.mk'_spec'_mk, map_one]
    refine nonpos_of_neg_nonneg (le_of_lt ?_)
    rwa [neg_neg, ← not_le]

theorem selfZPow_neg_mul (d : ℤ) : selfZPow x B (-d) * selfZPow x B d = 1 := by
  rw [mul_comm, selfZPow_mul_neg x B d]

theorem selfZPow_pow_sub (a : R) (b : B) (m d : ℤ) :
    selfZPow x B (m - d) * mk' B a (1 : Submonoid.powers x) = b ↔
      selfZPow x B m * mk' B a (1 : Submonoid.powers x) = selfZPow x B d * b := by
  rw [sub_eq_add_neg, selfZPow_add, mul_assoc, mul_comm _ (mk' B a 1), ← mul_assoc]
  constructor
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B d) h
    simp only at this
    rwa [mul_assoc, mul_assoc, selfZPow_neg_mul, mul_one, mul_comm b _] at this
  · intro h
    have := congr_arg (fun s : B => s * selfZPow x B (-d)) h
    simp only at this
    rwa [mul_comm _ b, mul_assoc b _ _, selfZPow_mul_neg, mul_one] at this

variable {R : Type*} [CommRing R] (x : R) (B : Type*) [CommRing B]
variable [Algebra R B] [IsLocalization.Away x B] [IsDomain R] [WfDvdMonoid R]

theorem exists_reduced_fraction' {b : B} (hb : b ≠ 0) (hx : Irreducible x) :
    ∃ (a : R) (n : ℤ), ¬x ∣ a ∧ selfZPow x B n * algebraMap R B a = b := by
  obtain ⟨⟨a₀, y⟩, H⟩ := surj (Submonoid.powers x) b
  obtain ⟨d, hy⟩ := (Submonoid.mem_powers_iff y.1 x).mp y.2
  have ha₀ : a₀ ≠ 0 := by
    haveI :=
      @isDomain_of_le_nonZeroDivisors B _ R _ _ _ (Submonoid.powers x) _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    simp only [map_zero, ← hy, map_pow] at H
    apply ((injective_iff_map_eq_zero' (algebraMap R B)).mp _ a₀).mpr.mt
    · rw [← H]
      apply mul_ne_zero hb (pow_ne_zero _ _)
      exact
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors B
          (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)
    · exact IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  simp only [← hy] at H
  obtain ⟨m, a, hyp1, hyp2⟩ := WfDvdMonoid.max_power_factor ha₀ hx
  refine ⟨a, m - d, ?_⟩
  rw [← mk'_one (M := Submonoid.powers x) B, selfZPow_pow_sub, selfZPow_natCast, selfZPow_natCast,
    ← map_pow _ _ d, mul_comm _ b, H, hyp2, map_mul, map_pow _ _ m]
  exact ⟨hyp1, congr_arg _ (IsLocalization.mk'_one _ _)⟩

end NumDen
