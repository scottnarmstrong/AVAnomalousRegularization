-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Intermediate.Weighted.WeightedEnergyPlane
import AVRegularity.CycleEvolution.CellTimeReverseAdmissibility
import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal
public import AVRegularity.Weighted.WordPredecessorFluxIdentity
public import AVRegularity.Weighted.WordMomentSlots

section
section
/-! A finite source budget gives a genuine scalar level with finite weighted energy. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_finite_weighted_scalar_level (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (κ : ι → ℕ) (Kmax : ℕ) (hκ : ∀ i, κ i ≤ Kmax)
    (ta S : ℝ) (hS : 0 ≤ S) (n : ℕ) (ϖ ρ strain : ℝ)
    (hρ : 0 < ρ) (hρh : ρ ≤ 1 / 2) (ha : 0 ≤ strain) (hsmall : strain * ρ ^ 2 ≤ 1 / 8)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (Cw : ℕ → ℝ) (hW : ChartWeights (fun t _ => G t) v ta S ϖ 0 n Cw)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i))
    (hf : geometryDataNorm π κ n ϖ 0 ρ f ≠ ⊤)
    (F : ∀ i, ℝ → PlaneHk Set.univ (κ i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc ta (ta + S))))
    (hFe : ∀ i, (∫⁻ t in Set.Icc ta (ta + S),
      weightedFactorialNormSq n ϖ 0 ρ (κ i) (F i t)) ≠ ⊤) :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (κ i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (κ i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => G t)) (fun _ i => κ i)
        ta (ta + S) v (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      geometryEnergyNorm π κ n ϖ 0 ρ ta (ta + S) u w < ⊤ := by
  classical
  obtain ⟨M, hM⟩ := hv.2.1
  have hb : ∃ C : ℝ, ∀ t ∈ Set.Icc ta (ta + S), ∀ x, ‖v t x‖ ≤ C := by
    refine ⟨|M|, fun t _ x => ?_⟩
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg M)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using CycleEvolution.cellDrift_entry_bound hM t x i
  have hmmap : Measurable (fun p : Set.Icc ta (ta + S) × Vec 2 => ((p.1 : ℝ), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  obtain ⟨C, _, hgate⟩ := Providers.weighted_energy_plane n Kmax (fun _ => 0) Cw
  have hresult := hgate π hπ κ hκ ta (ta + S) (by linarith) ρ 0 hρ (by norm_num)
    (by simp) v hb (hv.1.comp hmmap) (fun t _ => hvs t)
    (fun t _ => cellDrift_classical_divergence_zero hv hvs t)
    strain 1 1 ha (by norm_num) (by norm_num)
    (fun l hl hlK t _ x => by simpa only [one_pow, one_zpow, mul_one] using hjets l hl hlK t x)
    (by simpa only [one_mul, div_one] using hρh) (by simpa only [mul_one] using hsmall)
    (fun t _ => G t) g hg hg4 (hG.1.comp hmmap) (fun t _ z => hG.2.2.1 t z) hGn
    (fun _ _ _ _ => contDiff_const)
    (fun t _ z j hj _ a k => by
      rw [iteratedFDeriv_const_of_ne (by omega)]; simp)
    ta S ϖ 0 le_rfl le_rfl hW f F hF
  obtain ⟨u, w, hsol⟩ := hresult.1
  refine ⟨u, w, hsol, ?_⟩
  have hest := hresult.2.2 u w hsol
  have hflux := geometryFluxNorm_ne_top_of_components π κ n ϖ 0 ρ ta (ta + S) F hF hFe
  exact lt_of_le_of_lt hest (lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hflux⟩)))

end AVRegularity.Weighted
end
end

section
/-! Actual carrier data for one chronological scalar level. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

structure ScalarLevelState (κ : ι → ℕ) (h : ι → Type*)
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] where
  u : ∀ i, ℝ → PlaneHk Set.univ (κ i) (h i)
  w : ∀ i, ℝ → PlaneHk Set.univ (κ i + 1) (h i)
  F : ∀ i, ℝ → PlaneHk Set.univ (κ i) (PiLp 2 (fun _ : Fin 2 => h i))

def IsFiniteWeightedScalarLevel (π : ι → ℝ) (κ : ι → ℕ) (n : ℕ) (ϖ ρ ta S : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i)) (s : ScalarLevelState κ h) : Prop :=
  IsPlaneChainFrom (geometryScalarData 2 (fun t _ => G t)) (fun _ i => κ i)
    ta (ta + S) v (fun _ i => f i) (fun _ i => s.F i) (fun _ i => s.u i) (fun _ i => s.w i) ∧
  geometryEnergyNorm π κ n ϖ 0 ρ ta (ta + S) s.u s.w < ⊤

end AVRegularity.Weighted
end
end

section
/-! The chronological word starts from the supplied datum and has zero datum at every later level. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped Classical

namespace AVRegularity.Weighted

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N : ℕ}

def wordLevelDatum (κ : Fin (N + 1) → ι → ℕ)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) (j : Fin (N + 1)) (x : ι) :
    PlaneHk Set.univ (κ j x) (h x) :=
  if hj : j = 0 then (by subst hj; exact f x) else 0

@[simp] theorem wordLevelDatum_zero (κ : Fin (N + 1) → ι → ℕ)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) (x : ι) :
    wordLevelDatum κ f 0 x = f x := by
  simp [wordLevelDatum]

@[simp] theorem wordLevelDatum_succ (κ : Fin (N + 1) → ι → ℕ)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)) (j : Fin N) (x : ι) :
    wordLevelDatum κ f j.succ x = 0 := by
  simp [wordLevelDatum, Fin.succ_ne_zero]

end AVRegularity.Weighted
end
end
end

section
section
/-! The initial scalar level is solved with genuinely zero forcing. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_finite_weighted_scalar_initial (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (κ : ι → ℕ) (Kmax : ℕ) (hκ : ∀ i, κ i ≤ Kmax)
    (ta S : ℝ) (hS : 0 ≤ S) (n : ℕ) (ϖ ρ strain : ℝ)
    (hρ : 0 < ρ) (hρh : ρ ≤ 1 / 2) (ha : 0 ≤ strain) (hsmall : strain * ρ ^ 2 ≤ 1 / 8)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (Cw : ℕ → ℝ) (hW : ChartWeights (fun t _ => G t) v ta S ϖ 0 n Cw)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i))
    (hf : geometryDataNorm π κ n ϖ 0 ρ f ≠ ⊤)
 :
    ∃ s : ScalarLevelState κ h,
      IsFiniteWeightedScalarLevel π κ n ϖ ρ ta S G v f s ∧ s.F = 0 := by
  classical
  obtain ⟨u, w, hsol, he⟩ := exists_finite_weighted_scalar_level π hπ κ Kmax hκ
    ta S hS n ϖ ρ strain hρ hρh ha hsmall v hv hvs hjets G hG g hg hg4 hGn
    Cw hW f hf (fun _ _ => 0)
    (fun i => planeHk_zero_time_memLp (E := PiLp 2 (fun _ : Fin 2 => h i)) _ _)
    (fun i => by
      change (∫⁻ t in Set.Icc ta (ta + S), weightedFactorialNormSq n ϖ 0 ρ (κ i)
        (0 : PlaneHk Set.univ (κ i) (PiLp 2 (fun _ : Fin 2 => h i)))) ≠ ⊤
      simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top)
  exact ⟨⟨u, w, fun _ _ => 0⟩, ⟨hsol, he⟩, rfl⟩

end AVRegularity.Weighted
end
end

section
/-! A finite scalar level supplies the genuine source production used by the next letter. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarLevel_production_budget (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (κ : ι → ℕ) (n : ℕ) (ϖ ρ ta S : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i)) (s : ScalarLevelState κ h)
    (hs : IsFiniteWeightedScalarLevel π κ n ϖ ρ ta S G v f s) (i : ι) :
    MemLp (s.w i) 2 (volume.restrict (Set.Icc ta (ta + S))) ∧
      (∫⁻ t in Set.Icc ta (ta + S), weightedGradFactorialNormSq n ϖ 0 ρ (κ i) (s.w i t)) ≠ ⊤ := by
  refine ⟨hs.1.2.1 (0, i), ?_⟩
  exact (finite_mass_energy_components π hπ _ _ hs.2 i).2

end AVRegularity.Weighted
end
end

section
/-! Solve the next genuine scalar response driven by the literal preceding Taylor letter. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev

namespace AVRegularity.Weighted

variable {ι σ : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem exists_finite_weighted_scalar_successor (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (κ : σ → ℕ) (a b : ι → σ) (Kmax : ℕ) (hκ : ∀ x, κ (a x) ≤ Kmax)
    (ta S : ℝ) (hS : 0 ≤ S) (n : ℕ) (ϖ ρ strain : ℝ) (hϖ : 0 < ϖ)
    (hρ : 0 < ρ) (hρh : ρ ≤ 1 / 2) (ha : 0 ≤ strain) (hsmall : strain * ρ ^ 2 ≤ 1 / 8)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (Cw : ℕ → ℝ) (hW : ChartWeights (fun t _ => G t) v ta S ϖ 0 n Cw)
    (L : CycleLetter ι h D) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc ta (ta + S) ×ˢ Set.univ) J H)
    (hKJ : ∀ x, κ (a x) ≤ J) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ x u o (k : Fin (L.edge x u o).length), ∀ w X z,
      Measurable (fun t => ((L.edge x u o).get k).coeff w t X z))
    (fprev : ∀ x, PlaneHk Set.univ (κ (b x)) (h x))
    (s : ScalarLevelState (fun x => κ (b x)) h)
    (hs : IsFiniteWeightedScalarLevel π (fun x => κ (b x)) (n + L.slow)
      ϖ ρ ta S G v fprev s) :
    ∃ s' : ScalarLevelState (fun x => κ (a x)) h,
      IsFiniteWeightedScalarLevel π (fun x => κ (a x)) n ϖ ρ ta S G v (fun _ => 0) s' ∧
      ∀ x, ∀ᵐ t ∂(volume.restrict (Set.Icc ta (ta + S))),
        planeJetReadoutOperator (κ (a x)) (valueIndex2 (κ (a x))) (s'.F x t) =ᵐ[volume]
          letterAdmissibleFlux L κ (a x) b x (if L.positive then 1 else 0) X₀ δ
            (fun u => s.w u t) t := by
  classical
  have hprod (u : ι) := scalarLevel_production_budget π hπ (fun u => κ (b u))
    (n + L.slow) ϖ ρ ta S G v fprev s hs u
  have hex (x : ι) := exists_admissible_letter_flux_time π hπ L ta (ta + S) J H hL
    κ (a x) b x (hKJ x) (if L.positive then 1 else 0) n X₀ δ (hm x)
    ϖ hϖ ρ hρ s.w (fun u => (hprod u).1) (fun u => (hprod u).2)
  choose F hF hFe hFae using hex
  have hf0 : geometryDataNorm π (fun x => κ (a x)) n ϖ 0 ρ (fun _ => 0) ≠ ⊤ :=
    geometryDataNorm_ne_top_of_components (h := h) π _ n ϖ 0 ρ (fun _ => 0)
      (fun x => by rw [weightedFactorialNormSq_zero_carrier]; exact ENNReal.zero_ne_top)
  obtain ⟨u, w, hsol, he⟩ := exists_finite_weighted_scalar_level π hπ (fun x => κ (a x))
    Kmax hκ ta S hS n ϖ ρ strain hρ hρh ha hsmall v hv hvs hjets G hG g hg hg4 hGn
    Cw hW (fun _ => 0) hf0 F hF hFe
  refine ⟨⟨u, w, F⟩, ⟨hsol, he⟩, ?_⟩
  exact hFae

end AVRegularity.Weighted
end
end

section
/-! Assemble the genuine scalar solves, consuming precisely the slow degree at each step. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N D : ℕ}

theorem exists_finite_weighted_word_levels (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (κ : Fin (N + 1) → ι → ℕ) (Kmax : ℕ) (hκ : ∀ j x, κ j x ≤ Kmax)
    (ta S : ℝ) (hS : 0 ≤ S) (m : ℕ) (Ks : Fin N → ℕ)
    (ϖ ρ strain : ℝ) (hϖ : 0 < ϖ)
    (hρ : 0 < ρ) (hρh : ρ ≤ 1 / 2) (ha : 0 ≤ strain) (hsmall : strain * ρ ^ 2 ≤ 1 / 8)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (Cw : ℕ → ℝ) (hW : ∀ n, ChartWeights (fun t _ => G t) v ta S ϖ 0 n Cw)
    (letters : Fin N → CycleLetter ι h D) (hslow : ∀ j, (letters j).slow = Ks j)
    (J H : ℕ) (hL : ∀ j, IsCycleLetter π (letters j) (Set.Icc ta (ta + S) ×ˢ Set.univ) J H)
    (hKJ : ∀ (j : Fin N) x, κ j.succ x ≤ J) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ w X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff w t X z))
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (hf : geometryDataNorm π (κ 0) (wordReserveN m Ks) ϖ 0 ρ f ≠ ⊤) :
    ∃ s : ∀ j, ScalarLevelState (κ j) h,
      (∀ j, IsFiniteWeightedScalarLevel π (κ j) (wordMomentSlot m Ks j)
        ϖ ρ ta S G v (wordLevelDatum κ f j) (s j)) ∧
      (s 0).F = 0 ∧
      ∀ j x, ∀ᵐ t ∂(volume.restrict (Set.Icc ta (ta + S))),
        planeJetReadoutOperator (κ j.succ x) (valueIndex2 (κ j.succ x)) ((s j.succ).F x t)
          =ᵐ[volume]
        letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
          (j.succ, x) (fun u => (j.castSucc, u)) x
          (if (letters j).positive then 1 else 0) X₀ δ
          (fun u => (s j.castSucc).w u t) t := by
  classical
  let P := fun j (s : ScalarLevelState (κ j) h) =>
    IsFiniteWeightedScalarLevel π (κ j) (wordMomentSlot m Ks j) ϖ ρ ta S G v
      (wordLevelDatum κ f j) s ∧ (j = 0 → s.F = 0)
  let R := fun (j : Fin N) (s : ScalarLevelState (κ j.castSucc) h)
      (s' : ScalarLevelState (κ j.succ) h) =>
    ∀ x, ∀ᵐ t ∂(volume.restrict (Set.Icc ta (ta + S))),
      planeJetReadoutOperator (κ j.succ x) (valueIndex2 (κ j.succ x)) (s'.F x t)
        =ᵐ[volume]
      letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
        (j.succ, x) (fun u => (j.castSucc, u)) x
        (if (letters j).positive then 1 else 0) X₀ δ (fun u => s.w u t) t
  have h0 : ∃ s, P 0 s := by
    obtain ⟨s, hs, hz⟩ := exists_finite_weighted_scalar_initial π hπ (κ 0) Kmax (hκ 0)
      ta S hS (wordReserveN m Ks) ϖ ρ strain hρ hρh ha hsmall v hv hvs hjets
      G hG g hg hg4 hGn Cw (hW _) f hf
    refine ⟨s, ?_, fun _ => hz⟩
    rw [wordMomentSlot_zero, show wordLevelDatum κ f 0 = f from funext (wordLevelDatum_zero κ f)]
    exact hs
  have hstep : ∀ j s, P j.castSucc s → ∃ s', P j.succ s' ∧ R j s s' := by
    intro j s hs
    have hprev : IsFiniteWeightedScalarLevel π (κ j.castSucc)
        (wordMomentSlot m Ks j.succ + (letters j).slow) ϖ ρ ta S G v
        (wordLevelDatum κ f j.castSucc) s := by
      rw [hslow j, ← wordMomentSlot_castSucc]
      exact hs.1
    obtain ⟨s', hs', hr⟩ := exists_finite_weighted_scalar_successor π hπ
      (fun p : Fin (N + 1) × ι => κ p.1 p.2) (fun x => (j.succ, x))
      (fun x => (j.castSucc, x)) Kmax (hκ j.succ) ta S hS
      (wordMomentSlot m Ks j.succ) ϖ ρ strain hϖ hρ hρh ha hsmall v hv hvs hjets
      G hG g hg hg4 hGn Cw (hW _) (letters j) J H (hL j) (hKJ j) X₀ δ (hm j)
      (wordLevelDatum κ f j.castSucc) s hprev
    refine ⟨s', ⟨?_, ?_⟩, hr⟩
    · rw [show wordLevelDatum κ f j.succ = (fun _ => 0) from
        funext (wordLevelDatum_succ κ f j)]
      exact hs'
    · intro hj
      exact (Fin.succ_ne_zero j hj).elim
  obtain ⟨s, hs, hr⟩ := exists_finite_chronological_family (fun j => ScalarLevelState (κ j) h)
    P R h0 hstep
  exact ⟨s, fun j => (hs j).1, (hs 0).2 rfl, hr⟩

end AVRegularity.Weighted
end
end

section
/-! The chronological scalar forcing is the full native word flux almost everywhere. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N D : ℕ}

def wordScalarFlux (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (s : ∀ j, ScalarLevelState (κ j) h)
    (p : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h p.2) :=
  scalarChainFlux (fun t _ => G t) (fun _ => κ p.1)
    (fun q => (s p.1).w q.2 t) (0, p.2) t z +
    ((s p.1).F p.2 t).toFunction.jet (valueIndex2 (κ p.1 p.2)) z

theorem wordScalarFlux_agreement (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D)
    (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ a b : ℝ)
    (s : ∀ j, ScalarLevelState (κ j) h) (h0 : (s 0).F = 0)
    (hr : ∀ j x, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      planeJetReadoutOperator (κ j.succ x) (valueIndex2 (κ j.succ x)) ((s j.succ).F x t)
        =ᵐ[volume]
      letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
        (j.succ, x) (fun u => (j.castSucc, u)) x
        (if (letters j).positive then 1 else 0) X₀ δ
        (fun u => (s j.castSucc).w u t) t) :
    ∀ p : Fin (N + 1) × ι, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      wordChainRawFlux G letters κ X₀ δ (fun p => (s p.1).w p.2 t) p t
        =ᵐ[volume] wordScalarFlux G κ s p t := by
  classical
  have hd (p : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) :
      wordDiagonalFlux (D := D) G κ (fun p => (s p.1).w p.2 t) p t z =
      scalarChainFlux (fun t _ => G t) (fun _ => κ p.1)
        (fun q => (s p.1).w q.2 t) (0, p.2) t z := by
    apply (WithLp.equiv 2 _).injective
    funext k
    change wordDiagonalFlux (D := D) G κ (fun p => (s p.1).w p.2 t) p t z k =
      scalarChainFlux (fun t _ => G t) (fun _ => κ p.1)
        (fun q => (s p.1).w q.2 t) (0, p.2) t z k
    rw [wordDiagonalFlux_eq hD, scalarChainFlux_eq]
  rintro ⟨j, x⟩
  induction j using Fin.cases with
  | zero =>
    apply Filter.Eventually.of_forall
    intro t
    have hz := planeHk_zero_raw_jet (E := PiLp 2 (fun _ : Fin 2 => h x))
      (κ 0 x) (valueIndex2 (κ 0 x))
    filter_upwards [hz] with z hz
    rw [wordChainRawFlux_split, wordPredecessorFlux_zero, add_zero, hd]
    unfold wordScalarFlux
    rw [h0]
    simp only [Pi.zero_apply, hz, add_zero]
  | succ j =>
    filter_upwards [hr j x] with t ht
    have he := (planeJetReadout_ae_raw ((s j.succ).F x t)
      (valueIndex2 (κ j.succ x))).symm.trans ht
    filter_upwards [he] with z hz
    rw [wordChainRawFlux_split, hd, wordPredecessorFlux_succ]
    exact congrArg (_ + ·) hz.symm

end AVRegularity.Weighted
end
end

section
/-! Pack chronological solutions after setting the lifts to zero at exceptional times. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev

namespace AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N D : ℕ}

theorem word_native_solution_pack (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (κ : Fin (N + 1) → ι → ℕ)
    (X₀ : Vec 2) (δ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (s : ∀ j, ScalarLevelState (κ j) h)
    (hs : ∀ j, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => G t))
      (fun _ => κ j) a b v (fun _ => wordLevelDatum κ f j)
      (fun _ => (s j).F) (fun _ => (s j).u) (fun _ => (s j).w))
    (hflux : ∀ p : Fin (N + 1) × ι, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      wordChainRawFlux G letters κ X₀ δ (fun p => (s p.1).w p.2 t) p t
        =ᵐ[volume] wordScalarFlux G κ s p t) :
    ∃ w : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x),
      IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0)
        (fun j => (s j).u) w := by
  classical
  let good := fun t => ∀ p : Fin (N + 1) × ι,
    wordChainRawFlux G letters κ X₀ δ (fun p => (s p.1).w p.2 t) p t
      =ᵐ[volume] wordScalarFlux G κ s p t
  have hgood : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), good t := ae_all_iff.mpr hflux
  let w := fun j x t => if good t then (s j).w x t else 0
  have hw (j : Fin (N + 1)) (x : ι) : w j x =ᵐ[volume.restrict (Set.Icc a b)] (s j).w x :=
    hgood.mono (fun t ht => ite_eq_left ht)
  have hs' (j : Fin (N + 1)) := hs j
  unfold IsPlaneChainFrom IsCoupledWeakSolutionPlane at hs'
  refine ⟨w, ?_⟩
  unfold IsPlaneChain IsCoupledWeakSolutionPlane
  refine ⟨fun p => (hs' p.1).1 (0, p.2),
    fun p => ((hs' p.1).2.1 (0, p.2)).ae_eq (hw p.1 p.2).symm,
    ?_, ?_, ?_⟩
  · intro p
    filter_upwards [(hs' p.1).2.2.1 (0, p.2), hw p.1 p.2] with t ht hw
    simpa only [hw] using ht
  · intro p
    exact (hs' p.1).2.2.2.1 (0, p.2)
  · intro p t ht φ
    have hold := (hs' p.1).2.2.2.2 (0, p.2) t ht φ
    let du := fun r k => ((s p.1).w p.2 r).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (κ p.1 p.2))⟩, fun _ => k⟩
    let du' := fun r k => (w p.1 p.2 r).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (κ p.1 p.2))⟩, fun _ => k⟩
    let fl := fun r => scalarChainFlux (fun t _ => G t) (fun _ => κ p.1)
      (fun q => (s p.1).w q.2 r) (0, p.2) r
    let fl' := fun r => wordChainRawFlux G letters κ X₀ δ (fun p => w p.1 p.2 r) p r
    let ff := fun r => ((s p.1).F p.2 r).toFunction.jet (valueIndex2 (κ p.1 p.2))
    let zzF := fun _ : ℝ => (0 : PlaneHk Set.univ (κ p.1 p.2)
      (PiLp 2 (fun _ : Fin 2 => h p.2))).toFunction.jet (valueIndex2 (κ p.1 p.2))
    let zz := fun _ : ℝ => (0 : PlaneHk Set.univ (κ p.1 p.2) (h p.2)).toFunction.jet
      (valueIndex2 (κ p.1 p.2))
    let ph := φ.toFunction.jet (valueIndex2 1)
    let dph := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    have hzf := planeHk_zero_raw_jet (E := PiLp 2 (fun _ : Fin 2 => h p.2))
      (κ p.1 p.2) (valueIndex2 (κ p.1 p.2))
    have hzg := planeHk_zero_raw_jet (E := h p.2) (κ p.1 p.2) (valueIndex2 (κ p.1 p.2))
    have hegood (r : ℝ) (hr : good r) :
        weakIdentityRhs 1 v ph dph du' fl' zzF zz r =ᵐ[volume]
        weakIdentityRhs 1 v ph dph du fl ff zz r := by
      have hw0 : (fun q : Fin (N + 1) × ι => w q.1 q.2 r) =
          (fun q : Fin (N + 1) × ι => (s q.1).w q.2 r) := funext (fun _ => ite_eq_left hr)
      filter_upwards [hr p, hzf] with z hz hzF
      dsimp [weakIdentityRhs, du', du, fl', fl, ff, zzF, ph, dph]
      rw [hw0]
      simp only [w, ite_eq_left hr]
      change _ = _ at hz
      simp only [wordScalarFlux] at hz
      simp only [hz, hzF, Pi.zero_apply, PiLp.add_apply, PiLp.zero_apply, add_zero]
    have hebad (r : ℝ) (hr : ¬good r) :
        weakIdentityRhs 1 v ph dph du' fl' zzF zz r =ᵐ[volume] 0 := by
      have hw0 : (fun q : Fin (N + 1) × ι => w q.1 q.2 r) = (fun _ => 0) :=
        funext (fun _ => ite_eq_right hr)
      have hd := ae_all_iff.mpr (fun α : JetIndex2 (κ p.1 p.2 + 1) =>
        planeHk_zero_raw_jet (E := h p.2) (κ p.1 p.2 + 1) α)
      filter_upwards [wordChainRawFlux_zero G letters κ X₀ δ p r, hd, hzf, hzg]
        with z hz hd hzF hzG
      dsimp [weakIdentityRhs, du', fl', zzF, zz]
      rw [hw0]
      simp [w, ite_eq_right hr, hz, hd, hzF, hzG]
    have hold' : CoupledWeakIdentity (volume.restrict Set.univ) 1 a t v
        (((s p.1).u p.2 t).toFunction.jet (valueIndex2 (κ p.1 p.2)))
        ((wordLevelDatum κ f p.1 p.2).toFunction.jet (valueIndex2 (κ p.1 p.2)))
        ph dph du fl ff zz := by
      exact hold
    have hnew : ∀ r ∈ Set.Ioc a t,
        Integrable (weakIdentityRhs 1 v ph dph du' fl' zzF zz r) (volume.restrict Set.univ) := by
      intro r hr
      by_cases hg : good r
      · exact (hold'.2.2.1 r hr).congr (by simpa only [Measure.restrict_univ, weakIdentityRhs] using! (hegood r hg).symm)
      · exact (integrable_zero (Vec 2) ℝ (volume.restrict Set.univ)).congr
          (by simpa only [Measure.restrict_univ] using (hebad r hg).symm)
    have hae : ∀ᵐ r ∂(volume.restrict (Set.Ioc a t)),
        weakIdentityRhs 1 v ph dph du' fl' zzF zz r =ᵐ[volume.restrict Set.univ]
        weakIdentityRhs 1 v ph dph du fl ff zz r := by
      have hg := hgood.filter_mono (ae_mono (Measure.restrict_mono
        (show Set.Ioc a t ⊆ Set.Icc a b from fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩) le_rfl))
      exact hg.mono (fun r hr => by simpa only [Measure.restrict_univ] using hegood r hr)
    exact coupledWeakIdentity_rhs_transfer (volume.restrict Set.univ) 1 a t v _ _ ph dph
      du du' fl ff fl' zzF zz zz hold' hnew hae

end AVRegularity.Weighted
end
end
end
