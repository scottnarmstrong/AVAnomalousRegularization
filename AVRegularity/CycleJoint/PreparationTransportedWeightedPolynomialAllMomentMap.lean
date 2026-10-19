-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice
import AVRegularity.CycleJoint.ScalarPlaneUniformMassSquaredEnergy
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The true preparation native traces transfer across the renewal with the existing uniform reserved polynomial-moment price. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationReferenceCellTransitionOperator_renewal_polynomial_energy_le
    (s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (y₀ : Vec 2)
    (U : PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b)
    (n M Jmax : ℕ) (hn : n ≤ M) (hmax : J ≤ Jmax)
    (ϖ r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc' := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    weightedFactorialNormSq n ϖ 0 r J
      (preparationReferenceCellTransitionOperator hc hcover hTau ha J hJ
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
        (ocEpsilon q Λ m) he yc yc' t ht U) ≤
      ENNReal.ofReal (cellTransitionMomentBudget Jmax M) * weightedFactorialNormSq n ϖ 0 r J U := by
  intro seed yc yc'
  let V := preparationReferenceCellReturnOperator hc hcover hTau ha J hJ
    (ocEpsilon q Λ m) he yc t ht U
  have hh := preparationReferenceCellNativeCurve_renewal_polynomial_energy_le
    hc hcover hTau ha J hJ s hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hm hnext ν hν he y₀
    (fun _ => V) t ht n M Jmax hn hmax ϖ r hr hr1
  dsimp only at hh
  rw [preparationWindowReferenceCellNativeCurve_at_physical_time hc hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext ha J hJ ν hν (ocEpsilon q Λ m) he yc',
    preparationReferenceCellNativeCurve_at_physical_time hc hcover hTau ha J hJ
      ν hν (ocEpsilon q Λ m) he yc] at hh
  dsimp only [V] at hh
  rw [preparationReferenceCellPull_return hc hcover hTau ha J hJ
    (ocEpsilon q Λ m) he yc t ht U] at hh
  rw [preparationReferenceCellTransitionOperator_apply]
  exact hh
end

/-! The true preparation native traces transfer across the renewal with the existing uniform reserved polynomial-moment price. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)

theorem preparationReferenceCellTransitionOperator_renewal_family_energy_le
    (s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (y₀ : Vec 2)
    (U : ∀ i, PlaneHk univ (K i) (h i)) (π : ι → ℝ) (t : ℝ) (ht : t ∈ Icc a b)
    (n M Jmax : ℕ) (hn : n ≤ M) (hmax : ∀ i, K i ≤ Jmax)
    (ϖ r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc' := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
      (preparationReferenceCellTransitionOperator hc hcover hTau ha (K i) (hK i)
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
        (ocEpsilon q Λ m) he yc yc' t ht (U i))) ≤
      ENNReal.ofReal (cellTransitionMomentBudget Jmax M) *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i) := by
  intro seed yc yc'
  calc
    _ ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        (ENNReal.ofReal (cellTransitionMomentBudget Jmax M) *
          weightedFactorialNormSq n ϖ 0 r (K i) (U i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_right
        (preparationReferenceCellTransitionOperator_renewal_polynomial_energy_le
          hc hcover hTau ha (K i) (hK i) s hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hm hnext
          ν hν he y₀ (U i) t ht n M Jmax hn (hmax i) ϖ r hr hr1) _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
end

/-! The true preparation native traces transfer across the renewal with the existing uniform reserved polynomial-moment price. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationReferenceCellTransitionOperator_renewal_polynomial_energy_ne_top
    (s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (y₀ : Vec 2)
    (U : PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b)
    (n M Jmax : ℕ) (hn : n ≤ M) (hmax : J ≤ Jmax)
    (ϖ r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc' := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    weightedFactorialNormSq n ϖ 0 r J U ≠ ⊤ →
    weightedFactorialNormSq n ϖ 0 r J
      (preparationReferenceCellTransitionOperator hc hcover hTau ha J hJ
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
        (ocEpsilon q Λ m) he yc yc' t ht U) ≠ ⊤ := by
  intro seed yc yc' hfinite
  have hh := preparationReferenceCellTransitionOperator_renewal_polynomial_energy_le
    hc hcover hTau ha J hJ s hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hm hnext
    ν hν he y₀ U t ht n M Jmax hn hmax ϖ r hr hr1
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hh
end

/-! The true preparation native traces transfer across the renewal with the existing uniform reserved polynomial-moment price. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)

/-- The actual mixed chart transition acts slotwise as one native linear seam map. -/
def preparationReferenceCellTransitionFamilyLinearMap
    (σ : ℝ) (hσ : σ ∈ Icc a b) (e : ℝ) (he : e ≠ 0)
    (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b) :
    Module.End ℝ (∀ i, PlaneHk univ (K i) (h i)) :=
  LinearMap.pi (fun i =>
    (preparationReferenceCellTransitionOperator hc hcover hTau ha (K i) (hK i)
      σ hσ e he yc yc' t ht).toLinearMap.comp (LinearMap.proj i))

omit [Fintype ι] in
theorem preparationReferenceCellTransitionFamilyLinearMap_apply
    (σ : ℝ) (hσ : σ ∈ Icc a b) (e : ℝ) (he : e ≠ 0)
    (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : ∀ i, PlaneHk univ (K i) (h i)) (i : ι) :
    preparationReferenceCellTransitionFamilyLinearMap hc hcover hTau ha K hK
      σ hσ e he yc yc' t ht U i =
    preparationReferenceCellTransitionOperator hc hcover hTau ha (K i) (hK i)
      σ hσ e he yc yc' t ht (U i) := rfl

theorem preparationReferenceCellTransitionFamilyLinearMap_renewal_energy_le
    (s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (y₀ : Vec 2)
    (U : ∀ i, PlaneHk univ (K i) (h i)) (π : ι → ℝ) (t : ℝ) (ht : t ∈ Icc a b)
    (n M Jmax : ℕ) (hn : n ≤ M) (hmax : ∀ i, K i ≤ Jmax)
    (ϖ r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc' := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
      (preparationReferenceCellTransitionFamilyLinearMap hc hcover hTau ha K hK
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
        (ocEpsilon q Λ m) he yc yc' t ht U i)) ≤
      ENNReal.ofReal (cellTransitionMomentBudget Jmax M) *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i) := by
  intro seed yc yc'
  exact preparationReferenceCellTransitionOperator_renewal_family_energy_le
    hc hcover hTau ha K hK s hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hm hnext
    ν hν he y₀ U π t ht n M Jmax hn hmax ϖ r hr hr1

theorem preparationReferenceCellTransitionFamilyLinearMap_renewal_difference_energy_le
    (s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m)
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (y₀ : Vec 2)
    (U V : ∀ i, PlaneHk univ (K i) (h i)) (π : ι → ℝ) (t : ℝ) (ht : t ∈ Icc a b)
    (n M Jmax : ℕ) (hn : n ≤ M) (hmax : ∀ i, K i ≤ Jmax)
    (ϖ r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc' := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
      (preparationReferenceCellTransitionFamilyLinearMap hc hcover hTau ha K hK
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
        (ocEpsilon q Λ m) he yc yc' t ht U i -
        preparationReferenceCellTransitionFamilyLinearMap hc hcover hTau ha K hK
          (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
          (ocEpsilon q Λ m) he yc yc' t ht V i)) ≤
      ENNReal.ofReal (cellTransitionMomentBudget Jmax M) *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i - V i) := by
  intro seed yc yc'
  have hh := preparationReferenceCellTransitionFamilyLinearMap_renewal_energy_le
    hc hcover hTau ha K hK s hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hseq hm hnext
    ν hν he y₀ (U - V) π t ht n M Jmax hn hmax ϖ r hr hr1
  simpa only [map_sub, Pi.sub_apply] using hh
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The genuine homogeneous reference source is exactly the finite sum of the original constituent coefficient rows transported to that reference chart. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceNativeFluxOperator_eq_native_rows
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
      t ht v V = ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
        F.weight p t • WithLp.toLp 2 (fun k =>
          activePieceReferenceScalarRowOperator F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
            ν e E actual p v u γ t a b n hs hT he ht p.property (K u + 1) k
              (AVRegularity.CoupledEnergyPlane.mapPlaneHk (F.identity v u γ).map (V u))) := by
  rw [preparationReferenceNativeFluxOperator_apply, preparationPhysicalNativeFlux_eq_piece_sum]
  simp only [map_sum, map_smul]
  apply PiLp.ext
  intro k
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  rw [planeFluxChartPull_component]
  exact (preparation_active_piece_reference_scalar_row_transfer F hprep hcover hTau ha ν e E n hs
    actual hT he t ht p v u γ (K u + 1) (by have hh := hdesc v u γ; omega)
    (Nat.add_le_add_right (hK u) 1) k (V u)).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual identity-map assembly retains the original pointwise source price,
which is the price consumed by the mass Schur estimate. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem pointwiseOriginalIdentity_map_sum_density
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Ks Kmax : ℕ) (dom : F.Domain)
    (ν e E₀ ρ CR ζ : ℝ) (hν : 0 ≤ ν) (hE : 0 ≤ E₀) (hρ : 0 ≤ ρ)
    (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ) (v u : ι) (ϖ ρcell : ℝ) (μ : Measure ℝ)
    (T : F.Γ v u → X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) (K v) ϖ ρcell 0 μ)
    (B : X → ℝ → Vec 2 → ℝ) (hB : ∀ x, ∀ᵐ t ∂μ, ∀ z, 0 ≤ B x t z)
    (hb : ∀ γ x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρcell
        (planeTimeAllMomentCarrierToLp (K v) ϖ ρcell 0 μ (T γ x) t) z ≤
        pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E₀ ρ CR ζ v u γ ^ 2 * B x t z) :
    ∀ x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρcell
        (planeTimeAllMomentCarrierToLp (K v) ϖ ρcell 0 μ ((∑ γ, T γ) x) t) z ≤
        (∑ α : OriginalSourceIndex F v u,
          pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E₀ ρ CR ζ v u α) ^ 2 * B x t z := by
  have hh := planeAllMoment_map_sum_positive_price_density (K v) ϖ ρcell 0 μ T
    (fun γ => pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E₀ ρ CR ζ v u γ)
    (fun γ => pointwiseOriginalIdentityRemainderPrice_nonneg F K Ks Kmax dom ν e E₀ ρ CR ζ
      hν hE hρ hCR hζ v u γ) B hB hb
  simpa only [pointwiseOriginalIdentityRemainderPrice_sum_eq] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The genuine homogeneous reference source is exactly the finite sum of the original constituent coefficient rows transported to that reference chart. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationWindowReferenceNativeFluxOperator_eq_native_rows
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
      t ht v V = ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
        F.weight p t • WithLp.toLp 2 (fun k =>
          activePieceReferenceScalarRowOperator F hφ σ
            ν e E actual p v u γ t a b n hs hT he ht p.property (K u + 1) k
              (AVRegularity.CoupledEnergyPlane.mapPlaneHk (F.identity v u γ).map (V u))) := by
  rw [preparationWindowReferenceNativeFluxOperator_apply, preparationPhysicalNativeFlux_eq_piece_sum]
  simp only [map_sum, map_smul]
  apply PiLp.ext
  intro k
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  rw [planeFluxChartPull_component]
  exact (preparation_active_piece_window_reference_scalar_row_transfer F hprep hcover σ hσ ha ν e E n hs
    actual hT he t ht p v u γ (K u + 1) (by have hh := hdesc v u γ; omega)
    (Nat.add_le_add_right (hK u) 1) k (V u)).symm
end

/-! The actual reference source has the literal coupled coefficient array of the explicitly transformed family, with all original independent fields and identities retained. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceNativeFluxOperator_eq_reference_family_flux
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
      t ht v V = preparationPhysicalNativeFlux
        (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) K ν e E a b n
        (referenceChartedFamily_isSmoothOn_window F hφ _ a b E n hs) actual
        (referenceChartedFamily_isTorusCompatible F hφ _ E actual hT) he t ht v V := by
  rw [preparationReferenceNativeFluxOperator_eq_native_rows F K hdesc]
  apply PiLp.ext
  intro k
  simp only [preparationPhysicalNativeFlux, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply]
  rfl
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Compact scalar-direction tests give the literal chart transport correction in the actual material dual. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMaterialDual_compact_correction (a b : ℝ) (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ r, IsZ2Periodic (v r)) (t : ℝ) (ht : t ∈ Icc a b)
    (hvc : ∀ k, Continuous (fun x => v t x k))
    {M : ℝ} (hM : 0 ≤ M) (hvb : ∀ k x, |v t x k| ≤ M)
    (u : PlaneHk univ 1 E) (F : PlaneFluxL2 E)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (e : E) :
    inner ℝ (planeWeakDualRepresentative (planeMaterialTransport a b hab hφ s v hv hp t)
      (planeMaterialDiffusion a b hab hφ s ν t)
      (planeH1ChartPull hφ t s u) (planeFluxChartPull hφ t s F))
      (planeH1ChartPull hφ t s (compactSpacetimeVectorH1 f hf hs e t)) =
    inner ℝ (planeWeakDualRepresentative (planeScalarTransport (v t) hvc hM hvb)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) u F)
      (compactSpacetimeVectorH1 f hf hs e t) +
      ∫ x, f (t, x) * ∑ k : Fin 2, streamVel φ t x k *
        inner ℝ (planeH1GradientOperator u k x) e := by
  rw [planeMaterialDual_pair_eq_physical_plus_stream a b hab hφ s ν v hv hp t ht hvc hM hvb]
  congr 1
  apply integral_congr_ae
  filter_upwards [compactSpacetimeVectorH1_valueOperator_ae f hf hs e t] with x hx
  rw [hx]
  simp only [real_inner_smul_right, Fin.sum_univ_two]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The genuine reference source reads the literal coupled flux of the transformed original family on every rough energy carrier. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceNativeFluxOperator_reference_coupling_ae
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (k : Fin 2) :
    (preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
      t ht v V k : Vec 2 → h v) =ᵐ[volume] fun x =>
        AVRegularity.CoupledEnergyPlane.Variational.planeRawCouplingFlux K D t
          (edgeCoefficient (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m))
            ν e E actual K) V v x k := by
  rw [preparationReferenceNativeFluxOperator_eq_reference_family_flux F K hdesc]
  exact preparationPhysicalNativeFlux_ae
    (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) K ν e E a b n
    (referenceChartedFamily_isSmoothOn_window F hφ _ a b E n hs) actual
    (referenceChartedFamily_isTorusCompatible F hφ _ E actual hT) he t ht v V
    (referenceChartedFamily_isDescending F hφ _ K hdesc) k
end

/-! The actual reference source has the literal coupled coefficient array of the explicitly transformed family, with all original independent fields and identities retained. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationWindowReferenceNativeFluxOperator_eq_reference_family_flux
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
      t ht v V = preparationPhysicalNativeFlux
        (referenceChartedFamily F hφ σ) K ν e E a b n
        (referenceChartedFamily_isSmoothOn_window F hφ _ a b E n hs) actual
        (referenceChartedFamily_isTorusCompatible F hφ _ E actual hT) he t ht v V := by
  rw [preparationWindowReferenceNativeFluxOperator_eq_native_rows F K hdesc]
  apply PiLp.ext
  intro k
  simp only [preparationPhysicalNativeFlux, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply]
  rfl
end

/-! The genuine reference source reads the literal coupled flux of the transformed original family on every rough energy carrier. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationWindowReferenceNativeFluxOperator_reference_coupling_ae
    (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (V : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (k : Fin 2) :
    (preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
      t ht v V k : Vec 2 → h v) =ᵐ[volume] fun x =>
        AVRegularity.CoupledEnergyPlane.Variational.planeRawCouplingFlux K D t
          (edgeCoefficient (referenceChartedFamily F hφ σ)
            ν e E actual K) V v x k := by
  rw [preparationWindowReferenceNativeFluxOperator_eq_reference_family_flux F K hdesc]
  exact preparationPhysicalNativeFlux_ae
    (referenceChartedFamily F hφ σ) K ν e E a b n
    (referenceChartedFamily_isSmoothOn_window F hφ _ a b E n hs) actual
    (referenceChartedFamily_isTorusCompatible F hφ _ E actual hT) he t ht v V
    (referenceChartedFamily_isDescending F hφ _ K hdesc) k
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Genuine scalar estimates close finite weighted lift energy by triangular depth induction. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A homogeneous triangular plane solution preserves finite weighted lift moments. -/
theorem triangular_weighted_lift_time_energy_ne_top
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (D : ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) (hr1 : r ≤ 1)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm r (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (rank : ι → ℕ) (hz : ∀ i i', ¬ rank i' < rank i → ∀ d t x, A i i' d t x = 0)
    (hf : ∀ i, weightedFactorialNormSq m ϖ zc r (K i) (f i) ≠ ⊤) :
    ∀ i, (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (K i + 1) (w i s)) ≠ ⊤ := by
  let F := planeCouplingFluxRow hab r hr K D A hA hc w
  have hF (i : ι) : MemLp (F i) 2 (volume.restrict (Icc a b)) :=
    planeCouplingFluxRow_memLp hab r hr K D A hA hc w hAm hs.2.1 i
  have hscalar := planeHomogeneous_scalar_chain_solution hab r hr K D v A hA hc f u w hs
  have hsq : (fun x => planeMomentSquareRoot m ϖ zc x ^ 2) = planeMomentPolynomial m ϖ zc :=
    funext (planeMomentSquareRoot_sq m ϖ zc)
  have hAll (n : ℕ) : ∀ i, rank i = n →
      (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (K i + 1) (w i s)) ≠ ⊤ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hLower (i' : ι) (hlt : rank i' < rank i) :
          (∫⁻ s in Icc a b, storedChartFactorialEnergy r
            (fun x => planeMomentSquareRoot m ϖ zc x ^ 2) (w i' s)) ≠ ⊤ := by
        simpa only [hsq, weightedFactorialNormSq_stored_readout] using
          ih (rank i') (by omega) i' rfl
      have hrow := planeCouplingFluxRow_weighted_time_energy_ne_top_of_lower_depth
        hab r hr K D A hA hc w hAm hs.2.1
        (planeMomentSquareRoot m ϖ zc) (planeMomentSquareRoot_continuous m ϖ zc)
        (planeMomentSquareRoot_pos m ϖ zc) rank i (hz i) hLower
      have hFe : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (K i) (F i s)) ≠ ⊤ := by
        simpa only [hsq, weightedFactorialNormSq_stored_readout] using hrow
      exact identityScalar_weighted_lift_time_energy_ne_top a b hab (fun _ i => K i) Kmax
        (fun p => hK p.2) v hvm hv V strain B lam hV ha hB hlam hbv hjets
        (fun p => f p.2) (fun p => F p.2) (fun p => hF p.2)
        (fun p => u p.2) (fun p => w p.2) hscalar (0, i)
        t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb hr1 (hf i) hFe
  intro i
  exact hAll (rank i) i rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Original remainder prices give the actual native mass-energy error gain without a constituent or vertex count. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseOriginalRemainder_family_map_mass_moment_budget
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (K : ι → ℕ) (Ks Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ CR ζ : ℝ) (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ)
    (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hKs : Ks + 1 ≤ J)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (θ : ℝ) (hθ : 0 ≤ θ) (hrow : ∀ v, ∑ u, b v u ≤ θ)
    (hcol : ∀ u, ∑ v, b v u ≤ θ) (ϖ : ℝ) (μ : Measure ℝ)
    (L : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ)
    (W : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ)
    (hdensity : ∀ v u, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (L v u (W u)) t) z ≤
        (∑ α : OriginalSourceIndex F v u,
          pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α) ^ 2 *
            ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
              planeGradFactorialDensity (ρ / e)
                (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (W u) t) z))
    (n : ℕ) :
    (∫⁻ t, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (nativeFamilyEdgeForcingMap L v W) t) ∂μ) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) * (pointwiseOriginalRemainderGraphConstant Ks Kmax CR C * θ)) ^ 2) *
        ∫⁻ t, ∑ u, ENNReal.ofReal ((π u)⁻¹) *
          weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K u)
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (W u) t) ∂μ := by
  classical
  obtain ⟨hr, hc⟩ := pointwiseOriginalRemainderPrice_graph_budget_with_mass F π K Ks Kmax hK dom ν e E ρ CR ζ hCR hζ
    hν hE hρ C J b hKs henv hb θ hrow hcol
  exact planeAllMoment_edgeMap_mass_moment_budget K ϖ (ρ / e) μ L W π hπ
    (fun v u => ∑ α : OriginalSourceIndex F v u,
      pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α)
    (fun v u => Finset.sum_nonneg (fun α _ =>
      pointwiseOriginalRemainderPrice_nonneg F K Ks Kmax dom ν e E ρ CR ζ hν.le hE.le hρ.le hCR hζ v u α))
    (ζ ^ (Ks + 1) * (pointwiseOriginalRemainderGraphConstant Ks Kmax CR C * θ))
    (mul_nonneg (pow_nonneg hζ _)
      (mul_nonneg (pointwiseOriginalRemainderGraphConstant_nonneg Ks Kmax CR C) hθ))
    hr hc (Ks + 1) n hdensity

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Quantitative initial polynomial energy in the actual preparation reference
chart, with the center chosen as the inverse image of the physical patch center. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparationReference_localized_initial_family_return_energy_le
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1) (hab : a ≤ b)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (k : Fin 2 → ℤ) (f : ∀ i, TorusHk (K i) (h i))
    (π : ι → ℝ) (n : ℕ) (ϖ R ρ e Creturn : ℝ) (he : e ≠ 0)
    (hϖ : 0 ≤ ϖ / e) (hR : 0 ≤ R) (hmesh : (ϖ / e) / (N : ℝ) ≤ R)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) :
    let yc := streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (spatialPatchCenter N k) a
    ENNReal.ofReal ((Creturn * |e|) ^ 2) *
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
        (preparationReferenceCellLocalizedInitialFamilyLinearMap hc hcover hTau ha K hK
          hab hζ N hN k e he yc f i)) ≤
      ENNReal.ofReal (Creturn ^ 2) *
      ENNReal.ofReal ((1 + 2 * (preparationPieceFlowJetBudget Cchart
        (ocEpsilon q Λ (m - 1)) 1 * R) ^ 2) ^ n) *
      ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1)) ^ 2) *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * ENNReal.ofReal
        (factorialNormSq ρ (spatialPatchLocalization hζ N hN k (K i) (f i)).val) := by
  intro yc
  have hh := preparationReference_family_initial_return_energy_le hc hcover hTau ha hE
    K hK a (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hζ N hN k f π n ϖ R ρ e Creturn he
    hϖ hR hmesh hρ hρE
  simpa only [preparationReferenceCellLocalizedInitialFamilyLinearMap_apply] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Genuine scalar estimates close finite weighted lift energy by triangular depth induction. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Every homogeneous triangular plane solution has finite genuine weighted geometry energy. -/
theorem triangular_weighted_geometry_energy_lt_top
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (D : ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) (hr1 : r ≤ 1)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm r (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (rank : ι → ℕ) (hz : ∀ i i', ¬ rank i' < rank i → ∀ d t x, A i i' d t x = 0)
    (hf : ∀ i, weightedFactorialNormSq m ϖ zc r (K i) (f i) ≠ ⊤) (π : ι → ℝ) :
    geometryEnergyNorm π K m ϖ zc r a b u w < ⊤ := by
  have hlift := triangular_weighted_lift_time_energy_ne_top a b hab K D Kmax hK
    v hvm hv V strain B lam hV ha hB hlam hbv hjets
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb hr1
    A hA hc hAm f u w hs rank hz hf
  let F := planeCouplingFluxRow hab r hr K D A hA hc w
  have hF (i : ι) : MemLp (F i) 2 (volume.restrict (Icc a b)) :=
    planeCouplingFluxRow_memLp hab r hr K D A hA hc w hAm hs.2.1 i
  have hscalar := planeHomogeneous_scalar_chain_solution hab r hr K D v A hA hc f u w hs
  have hsq : (fun x => planeMomentSquareRoot m ϖ zc x ^ 2) = planeMomentPolynomial m ϖ zc :=
    funext (planeMomentSquareRoot_sq m ϖ zc)
  have hstored (i : ι) : (∫⁻ s in Icc a b, storedChartFactorialEnergy r
      (fun x => planeMomentSquareRoot m ϖ zc x ^ 2) (w i s)) ≠ ⊤ := by
    simpa only [hsq, weightedFactorialNormSq_stored_readout] using hlift i
  have hrow (i : ι) := planeCouplingFluxRow_weighted_time_energy_ne_top
    hab r hr K D A hA hc w hAm hs.2.1
    (planeMomentSquareRoot m ϖ zc) (planeMomentSquareRoot_continuous m ϖ zc)
    (planeMomentSquareRoot_pos m ϖ zc) hstored i
  have hFe (i : ι) : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (K i) (F i s)) ≠ ⊤ := by
    simpa only [hsq, weightedFactorialNormSq_stored_readout] using hrow i
  have he (i : ι) := identityScalar_weighted_value_gradient_energy_ne_top
    a b hab (fun _ i => K i) Kmax (fun p => hK p.2)
    v hvm hv V strain B lam hV ha hB hlam hbv hjets
    (fun p => f p.2) (fun p => F p.2) (fun p => hF p.2)
    (fun p => u p.2) (fun p => w p.2) hscalar (0, i)
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb (hf i) (hFe i)
  apply lt_top_iff_ne_top.mpr
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  apply ENNReal.sum_ne_top.mpr
  intro i _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he i)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Positive piece assembly and a fixed finite order sum retain the original
source-index price. The order count enters only the family-independent chart
constant; neither pieces nor identities contribute a counting loss. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem pointwiseOriginalIdentity_piece_order_sum_density
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Ks Kmax M : ℕ) (dom : F.Domain)
    (ν e E₀ ρ CR ζ : ℝ) (hν : 0 ≤ ν) (hE : 0 ≤ E₀) (hρ : 0 ≤ ρ)
    (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ) (v u : ι) (s ϖ ρcell : ℝ) (μ : Measure ℝ)
    (S : Finset P)
    (T : F.Γ v u → Fin M → S →
      X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) (K v) ϖ ρcell 0 μ)
    (B : X → ℝ → Vec 2 → ℝ) (hB : ∀ x, ∀ᵐ t ∂μ, ∀ z, 0 ≤ B x t z)
    (hb : ∀ γ r p x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρcell
        (planeTimeAllMomentCarrierToLp (K v) ϖ ρcell 0 μ (T γ r p x) t) z ≤
        F.weight p.val (s * t) ^ 2 *
          (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E₀ ρ CR ζ v u γ ^ 2 *
            B x t z)) :
    ∀ x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρcell
        (planeTimeAllMomentCarrierToLp (K v) ϖ ρcell 0 μ
          ((∑ γ, ∑ r, ∑ p, T γ r p) x) t) z ≤
        (∑ α : OriginalSourceIndex F v u,
          pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E₀ ρ
            ((M : ℝ) * CR) ζ v u α) ^ 2 * B x t z := by
  classical
  have hp (γ : F.Γ v u) := pointwiseOriginalIdentityRemainderPrice_nonneg
    F K Ks Kmax dom ν e E₀ ρ CR ζ hν hE hρ hCR hζ v u γ
  have hpiece (γ : F.Γ v u) (r : Fin M) :=
    familyPositive_allMoment_map_density_le F S (K v) s ϖ ρcell 0 μ (T γ r)
      (fun x t z =>
        pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E₀ ρ CR ζ v u γ ^ 2 *
          B x t z)
      (fun x => (hB x).mono (fun t ht z => mul_nonneg (sq_nonneg _) (ht z)))
      (hb γ r)
  have horder (γ : F.Γ v u) := planeAllMoment_map_sum_positive_price_density
    (K v) ϖ ρcell 0 μ (fun r : Fin M => ∑ p, T γ r p)
    (fun _ => pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E₀ ρ CR ζ v u γ)
    (fun _ => hp γ) B hB (hpiece γ)
  apply pointwiseOriginalIdentity_map_sum_density F K Ks Kmax dom ν e E₀ ρ
    ((M : ℝ) * CR) ζ hν hE hρ (mul_nonneg (Nat.cast_nonneg _) hCR) hζ
    v u ϖ ρcell μ (fun γ => ∑ r, ∑ p, T γ r p) B hB
  intro γ
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pointwiseOriginalIdentityRemainderPrice_mul_chart_price] using horder γ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.ChartTransport AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Certified Piola transport constructs actual native maps for polynomial remainder arrays. -/

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem exists_preparationTransportedPolynomial_weighted_allMoment_map
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1))
    (s t : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |t - s| ≤ 2 * Cage * ocTauPP α q Λ m)
    (N Dγ : ℕ) (hN : N ≤ Jchart) (hKN : K + Dγ ≤ N)
    (e ρ ϖ : ℝ) (he : 0 < e) (hρ : 0 < ρ) (hϖ : 0 < ϖ)
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1) / e) (yc : Vec 2) (μ : Measure ℝ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2)
    (hBm : ∀ d I i z, Measurable (fun τ => B d I τ z i))
    (hBs : ∀ d I i τ, ContDiff ℝ (K : ℕ) (fun z => B d I τ z i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hMB : ∀ d I, 0 ≤ MB d I) (p : ℕ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i τ j, j ≤ K → ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I τ x i) z‖ ≤ MB d I * polynomialMomentRoot ϖ z ^ p)
    (Cmap : U →L[ℝ] V) (w : ℝ → ℝ) (hwm : Measurable w) (hw : ∀ τ, |w τ| ≤ 1) :
    ∃ T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ,
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
        (fun x τ z => nativeArrayAssembly r Cmap
          (fun a A => w τ * transportedCoeff (fun y => naturalPreparationJacobian hφ s t (yc + e • y))
            Dγ (fun d I => B d I τ z) r A z a)
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x τ) r I z))) T := by
  let J := fun y => naturalPreparationJacobian hφ s t (yc + e • y)
  let c := fun a A τ z => transportedCoeff J Dγ (fun d I => B d I τ z) r A z a
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let C := compConst Cflow N * Cflow
  let R := ocEpsilon q Λ (m - 1) / e
  have hCf : 1 ≤ Cflow := one_le_jetConst _ _
  have hC : 0 ≤ C := mul_nonneg (compConst_nonneg hCf N) (zero_le_one.trans hCf)
  have hR : 0 < R := div_pos hE he
  have hJ i j : ContDiff ℝ (⊤ : ℕ∞) (fun y => J y i j) :=
    ((naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)).comp (contDiff_const.add (contDiff_id.const_smul e))
  have hcm a A z : Measurable (fun τ => c a A τ z) := by
    dsimp only [c]
    unfold transportedCoeff
    apply Finset.measurable_fun_sum
    intro d _
    apply Finset.measurable_fun_sum
    intro I _
    apply Finset.measurable_fun_sum
    intro i _
    exact ((hBm d I i z).const_mul _).mul_const _
  have hcs a A τ : ContDiff ℝ (K : ℕ) (c a A τ) :=
    transportedCoeff_spatial_smooth J hJ Dγ K (fun d I z => B d I τ z)
      (fun d I i => hBs d I i τ) r A a
  let price := transportedPolynomialJetPrice N Dγ r K C R MB
  have hprice : 0 ≤ price := transportedPolynomialJetPrice_nonneg N Dγ r K C R hC hR.le MB hMB
  have hcb a A : ∀ᵐ τ ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c a A τ) z‖ ≤ price * polynomialMomentRoot ϖ z ^ p := by
    apply Filter.Eventually.of_forall
    intro τ j hj z
    exact preparationTransportedPolynomial_coefficient_jet_budget K r hc ha hE s t hs ht hage
      N Dγ hN hKN e ρ ϖ he hρ hρE yc B hBs MB hMB p hBj τ j hj A a z
  exact exists_planeWeightedNativeArrayPolynomial_allMoment_map hKL hr p ϖ ρ hϖ hρ μ c hcm hcs Cmap
    (fun _ _ => price) (fun _ _ => hprice) hcb w hwm hw

end AVRegularity.CycleJointProofs
end
end
