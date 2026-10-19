-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainSmoothFluxIBP
import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
public import AVRegularity.CoupledEnergy.Galerkin.PlainHigherSynthesis
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Move the actual energy test onto weak value and flux source derivatives. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The value pairing with the finite energy test is the actual differentiated value pairing. -/
theorem plainEnergyTest_value_pairing {K r : ℕ} (hr : r ≤ K) (N : ℕ) (i : ι)
    (w : DerivativeWord2 r) (c : CoupledPlainCoefficients (h := h) N) (f : TorusHk K (h i)) :
    inner ℝ (f.val (valueIndex2 K))
      ((coupledPlainSynthesis N i 0 (plainEnergyTest N i w c)).val (valueIndex2 0)) =
      inner ℝ (f.val ⟨⟨r, by omega⟩, w⟩) ((coupledPlainSynthesis N i K c).val ⟨⟨r, by omega⟩, w⟩) := by
  rw [plainEnergyTest_synthesis_self]
  change inner ℝ (f.val (valueIndex2 K))
    ((-1 : ℝ) ^ r • (coupledPlainSynthesis N i 0
      (plainDerivativeCoefficients N 0 w (plainDerivativeCoefficients N 0 w c))).val (valueIndex2 0)) = _
  rw [real_inner_smul_right]
  have hibp := plainWeakJet_test_word_ibp hr N (plainDerivativeCoefficients N 0 w c) i f w
  rw [plainDerivativeCoefficients_value_eq_jet hr] at hibp
  exact hibp.symm

/-- Flux testing differentiates the weak flux and retains one extra derivative on the finite field. -/
theorem plainEnergyTest_flux_direction_pairing {K r : ℕ} (hr : r ≤ K) (N : ℕ) (i : ι)
    (w : DerivativeWord2 r) (k : Fin 2) (c : CoupledPlainCoefficients (h := h) N)
    (f : TorusHk K (h i)) :
    inner ℝ (f.val (valueIndex2 K))
      ((coupledPlainSynthesis N i 1 (plainEnergyTest N i w c)).val
        ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) =
      inner ℝ (f.val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i (K + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩) := by
  rw [plainEnergyTest_synthesis_self]
  change inner ℝ (f.val (valueIndex2 K))
    ((-1 : ℝ) ^ r • (coupledPlainSynthesis N i 1
      (plainDerivativeCoefficients N 0 w (plainDerivativeCoefficients N 0 w c))).val
        ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) = _
  rw [real_inner_smul_right,
    ← plainDerivativeCoefficients_value_eq_jet (K := 1) (by omega) N (fun _ : Fin 1 => k),
    plainDerivativeCoefficients_snoc,
    ← plainDerivativeCoefficients_direction_word]
  have hibp := plainWeakJet_test_word_ibp hr N
    (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) (plainDerivativeCoefficients N 0 w c)) i f w
  rw [plainDerivativeCoefficients_snoc,
    plainDerivativeCoefficients_value_eq_jet (K := K + 1) (by omega)] at hibp
  rw [plainDerivativeCoefficients_snoc]
  exact hibp.symm

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Scalar dot tests of initial Fourier coefficients, including directional
flux tests. These identities transfer the finite primitive energy back to
the actual weak Sobolev value and flux fields. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainInitialCoefficients_dot_pairing (N : ℕ) (K L : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (z : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainInitialCoefficients N K f a * z a) =
      ∑ i, inner ℝ (torusHkValueCLM (f i))
        (torusHkValueCLM (coupledPlainSynthesis N i (L i) z)) := by
  simpa only [plainCoefficientTestCLM_apply, mul_comm] using
    plainInitialCoefficients_test_pairing N K L f z

/-- A directional finite derivative test is exactly the weak flux coordinate pairing. -/
theorem plainInitialFlux_direction_dot (N : ℕ) (K : ι → ℕ) (k : Fin 2)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (z : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainInitialCoefficients N K
      (fun i => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i)) a *
        plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) z a) =
      ∑ i, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) ((F i).val (valueIndex2 (K i))))
        ((coupledPlainSynthesis N i 1 z).val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) := by
  rw [plainInitialCoefficients_dot_pairing N K (fun _ => 0)]
  apply Finset.sum_congr rfl
  intro i _
  have hm := mapTorusHk_jet_eq_compLp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i) (valueIndex2 (K i))
  have hd := plainDerivativeCoefficients_value_eq_jet (K := 1) (by omega)
    N (fun _ : Fin 1 => k) z i
  change inner ℝ ((mapTorusHk _ (F i)).val (valueIndex2 (K i)))
    ((coupledPlainSynthesis N i 0 (plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) z)).val
      (valueIndex2 0)) = _
  rw [hm, hd]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual integrated finite spatial equation against the Fourier cutoff
of an arbitrary periodic H¹ test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The finite ODE gives the literal spatial equation against every projected H¹ test. -/
theorem plainODE_projected_weak_equation (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hv : ∀ s ∈ Icc a b, Continuous (v s))
    (hA : ∀ s ∈ Icc a b, ∀ i i' d, Continuous (A i i' d s))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (f : ∀ i, TorusHk (K i) (h i)) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N K f) a b y)
    (hint : IntervalIntegrable (linearRhs
      (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s)) y) volume a b)
    (φ : ∀ i, TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (y t)))
      (torusHkValueCLM (galerkinProj N (φ i)))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N (φ i)))) =
    ∫ s in a..t,
      (∫ x in AVenhance.unitCube, plainSpatialTestIntegrand N D ν K (v s)
        (fun i i' d => A i i' d s) (y s) (plainInitialCoefficients N (fun _ => 1) φ) x) +
      (∫ x in AVenhance.unitCube, plainForcingTestIntegrand N
        (plainInitialCoefficients N (fun _ => 1) φ)
        (fun i => torusHkValueCLM (F i s)) (fun i => torusHkValueCLM (g i s)) x) := by
  have hid := plainODE_projected_test_spatial_equation N D ν K hab v A hv hA F g f y hy hint φ t ht
  rw [hid]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  have hs' : s ∈ Icc a b := by
    rw [uIoc_of_le ht.1] at hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  simp only [mul_add, Finset.sum_add_distrib]
  rw [plainSpatialTest_integral_contraction N D ν K (v s) (hv s hs')
    (fun i i' d => A i i' d s) (hA s hs'), plainForcingTest_integral_contraction]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The finite weak source is the Fourier projection of the value source
plus the directional divergence of the projected flux. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourceCoefficients_derivative_dot (N : ℕ) (K : ι → ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) (z : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainSourceCoefficients N K F g a * z a) =
      (∑ a, plainInitialCoefficients N K g a * z a) +
      ∑ k : Fin 2, ∑ a,
        plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k)
          (plainInitialCoefficients N K
            (fun i => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))) a * z a := by
  rw [plainSourceCoefficients_pairing]
  have hvalue := plainInitialCoefficients_dot_pairing N K (fun _ => 1) g z
  change _ = ∑ i, inner ℝ ((g i).val (valueIndex2 (K i)))
    ((coupledPlainSynthesis N i 1 z).val (valueIndex2 1)) at hvalue
  rw [← hvalue]
  rw [Finset.sum_comm]
  simp_rw [← plainInitialFlux_direction_dot N K]
  have hskew (k : Fin 2) :
      (∑ a, plainInitialCoefficients N K
        (fun i => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i)) a *
          plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) z a) =
      -(∑ a, plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k)
        (plainInitialCoefficients N K
          (fun i => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))) a * z a) := by
    have hs := plainDerivativeCoefficients_direction_skew N k
      (plainInitialCoefficients N K
        (fun i => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))) z
    linarith
  simp_rw [hskew]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]

/-- The native source vector is projected value forcing plus projected flux divergence. -/
theorem plainSourceCoefficients_eq_value_add_divergence (N : ℕ) (K : ι → ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) :
    plainSourceCoefficients N K F g = fun a => plainInitialCoefficients N K g a +
      ∑ k : Fin 2, plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k)
        (plainInitialCoefficients N K
          (fun i => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))) a := by
  funext a
  have hs := plainSourceCoefficients_derivative_dot N K F g (Pi.single a 1)
  simpa [Pi.single_apply] using hs

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual integrated finite spatial equation against the Fourier cutoff
of an arbitrary periodic H¹ test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Original coefficient and forcing assumptions discharge the finite RHS integrability. -/
theorem plainFourier_projected_weak_equation_of_data (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hv_bdd : ∃ V : ℝ, ∀ s ∈ Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (hv_meas : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hv : ∀ s ∈ Icc a b, Continuous (v s))
    (hA : ∀ s ∈ Icc a b, ∀ i i' d, Continuous (A i i' d s))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (f : ∀ i, TorusHk (K i) (h i)) (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b)))
    (y : C(Icc a b, CoupledPlainCoefficients (h := h) N))
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N K f) a b (extendCurve hab y))
    (φ : ∀ i, TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (extendCurve hab y t)))
      (torusHkValueCLM (galerkinProj N (φ i)))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N (φ i)))) =
    ∫ s in a..t,
      (∫ x in AVenhance.unitCube, plainSpatialTestIntegrand N D ν K (v s)
        (fun i i' d => A i i' d s) (extendCurve hab y s) (plainInitialCoefficients N (fun _ => 1) φ) x) +
      (∫ x in AVenhance.unitCube, plainForcingTestIntegrand N
        (plainInitialCoefficients N (fun _ => 1) φ)
        (fun i => torusHkValueCLM (F i s)) (fun i => torusHkValueCLM (g i s)) x) := by
  obtain ⟨C, hC, hbound⟩ := plainIntervalMatrix_bounded N D ν ρ hρ K a b hab v hv_bdd A hA_bdd
  have hm : ∀ r c, AEStronglyMeasurable
      (fun s => plainIntervalMatrix N D ν K a b hab v A s r c) volume := fun r c =>
    (plainIntervalMatrix_stronglyMeasurable N D ν K a b hab v hv_meas A hA_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (plainSourceCoefficients_integrable N K a b F g hF hg)
  have hint := plainMatrixODE_rhs_intervalIntegrable hab (plainIntervalMatrix N D ν K a b hab v A)
    _ (plainInitialCoefficients N K f) C hC hm hbound hf y
  have hint' := plainIntervalRhs_intervalIntegrable N D ν K a b hab v A _ _ hint
  exact plainODE_projected_weak_equation N D ν K hab v A hv hA F g f (extendCurve hab y)
    hy hint' φ t ht

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Exact differentiated energy contribution of the actual flux and value forcing. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Differentiated finite source testing gives the genuine weak value and flux jet pairings. -/
theorem plainSourceCoefficients_energy_pairing (N : ℕ) (K : ι → ℕ) (i : ι)
    {r : ℕ} (hr : r ≤ K i) (w : DerivativeWord2 r)
    (F : ∀ j, TorusHk (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (g : ∀ j, TorusHk (K j) (h j)) (c : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainSourceCoefficients N K F g a * plainEnergyTest N i w c a) =
      inner ℝ ((g i).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i (K i) c).val ⟨⟨r, by omega⟩, w⟩) -
      ∑ k : Fin 2, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) ((F i).val ⟨⟨r, by omega⟩, w⟩))
        ((coupledPlainSynthesis N i (K i + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩) := by
  rw [plainSourceCoefficients_pairing]
  congr 1
  · rw [Finset.sum_eq_single i]
    · rw [coupledPlainSynthesis_value_order_independent N i 1 0,
        plainEnergyTest_value_pairing hr]
    · intro j _ hji
      rw [plainEnergyTest_synthesis_other N i j hji]
      change inner ℝ _ (0 : ComponentL2 (volume.restrict AVenhance.unitCube) (h j)) = 0
      exact inner_zero_right _
    · simp
  · rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro k _
      let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k
      have he := plainEnergyTest_flux_direction_pairing hr N i w k c (mapTorusHk P (F i))
      simp only [mapTorusHk_jet_eq_compLp] at he
      exact he
    · intro j _ hji
      apply Finset.sum_eq_zero
      intro k _
      rw [plainEnergyTest_synthesis_other N i j hji]
      change inner ℝ _ (0 : ComponentL2 (volume.restrict AVenhance.unitCube) (h j)) = 0
      exact inner_zero_right _
    · simp

end AVRegularity.CoupledEnergy.Galerkin
end
