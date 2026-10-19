-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertSobolevOperator
import AVRegularity.CoupledEnergyPlane.Fourier.BandJetOperator
import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The same actual plane cutoff field supplies compatible Sobolev carriers at all orders. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbertBandHk_truncate (N K L : ℕ) (hKL : K ≤ L)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    truncatePlaneHk hKL (hilbertBandHk N L u) = hilbertBandHk N K u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  simp only [truncatePlaneHk_apply, hilbertBandHk_component]
  rfl
end

/-! Sobolev truncation preserves the literal spatial value class. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeHkValueOperator_truncate {K L : ℕ} (hKL : K ≤ L) (w : PlaneHk Set.univ L E) :
    planeHkValueOperator (E := E) K (truncatePlaneHk hKL w) = planeHkValueOperator (E := E) L w := by
  rw [planeHkValueOperator_apply, planeHkValueOperator_apply, truncatePlaneHk_apply]
  rfl
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier LineDeriv Filter
open AVRegularity.Analysis.Convolution
open scoped SchwartzMap Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The literal source weak derivative is the actual tempered-distribution
derivative. A normalized compact mollifier and strong L² convergence prove
the statement for arbitrary weak L² inputs. -/

/-- Compact-test weak derivatives and L² determine the actual distribution derivative. -/
theorem coordinate_lineDerivOp_of_weakPartial
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hw : HasWeakPartialDerivOn Set.univ i f g) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (ofRealL2 volume f) : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) =
        ((coordinateL2Equiv (ofRealL2 volume g) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) := by
  obtain ⟨κ, hc, hd, hκ, hmass⟩ := exists_normalized_smooth_kernel
  obtain ⟨R, hzero⟩ := exists_shrinking_linearEquiv
  apply coordinate_lineDerivOp_closed i (tendsto_averagingOperator_of_tendsto_zero
      (fun n => (R n).toLinearEquiv.toAddHom) (fun n => (R n).continuous) hzero hκ hmass f)
    (tendsto_averagingOperator_of_tendsto_zero
      (fun n => (R n).toLinearEquiv.toAddHom) (fun n => (R n).continuous) hzero hκ hmass g)
  intro n
  exact coordinate_lineDerivOp_averaging_weak f g i hw (R n) hc hd

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Linear energy pairing identities for the actual plane Fourier readout. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandPairing_neg (N K : ℕ) (ρ : ℝ)
    (u q : Lp E 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ (hilbertBandHk N K (-u)).val (hilbertBandHk N K q).val =
      -factorialPairing ρ (hilbertBandHk N K u).val (hilbertBandHk N K q).val := by
  change factorialPairing ρ (bandJetOperator N K (-u)) (bandJetOperator N K q) = _
  rw [map_neg, factorialPairing_neg_left]
  rfl

theorem bandPairing_add (N K : ℕ) (ρ : ℝ)
    (u v q : Lp E 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ (hilbertBandHk N K (u + v)).val (hilbertBandHk N K q).val =
      factorialPairing ρ (hilbertBandHk N K u).val (hilbertBandHk N K q).val +
      factorialPairing ρ (hilbertBandHk N K v).val (hilbertBandHk N K q).val := by
  change factorialPairing ρ (bandJetOperator N K (u + v)) (bandJetOperator N K q) = _
  rw [map_add, factorialPairing_add_left]
  rfl

theorem bandPairing_smul (N K : ℕ) (ρ c : ℝ)
    (u q : Lp E 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ (hilbertBandHk N K (c • u)).val (hilbertBandHk N K q).val =
      c * factorialPairing ρ (hilbertBandHk N K u).val (hilbertBandHk N K q).val := by
  change factorialPairing ρ (bandJetOperator N K (c • u)) (bandJetOperator N K q) = _
  rw [map_smul, factorialPairing_smul_left]
  rfl

theorem bandPairing_sum {J : Type*} (s : Finset J) (N K : ℕ) (ρ : ℝ)
    (u : J → Lp E 2 (volume : Measure (Vec 2)))
    (q : Lp E 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ (hilbertBandHk N K (∑ j ∈ s, u j)).val (hilbertBandHk N K q).val =
      ∑ j ∈ s, factorialPairing ρ (hilbertBandHk N K (u j)).val (hilbertBandHk N K q).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [factorialPairing, hilbertBandHk_component]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, bandPairing_add, ih]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The literal real spectral approximation preserves source weak derivative
pairs, with no regularity premise beyond their actual weak L² identity. -/

theorem realFrequencyBall_projection_hasWeakPartialDeriv
    (N : ℕ) (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hw : HasWeakPartialDerivOn Set.univ i f g) :
    HasWeakPartialDerivOn Set.univ i
      (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N) f)
      (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N) g) := by
  have hd := lineDerivOp_band_projection N
    (coordinateL2Equiv (ofRealL2 volume f)) (coordinateL2Equiv (ofRealL2 volume g))
    (coordinateVector i) (coordinate_lineDerivOp_of_weakPartial f g i hw)
  rw [← coordinate_frequency_projection, ← coordinate_frequency_projection,
    ← ofRealL2_realSpectralProjection _ _ (frequencyBall_neg N),
    ← ofRealL2_realSpectralProjection _ _ (frequencyBall_neg N)] at hd
  have h := hasWeakPartialDerivOn_re_of_distribution _ _ i hd
  apply AVRegularity.Sobolev.hasWeakPartialDerivOn_congr_ae _ _ h
  · filter_upwards [show ofRealL2 volume
      (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N) f)
        =ᵐ[volume.restrict Set.univ] (fun x =>
          ((realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N) f) x : ℂ))
      from by simpa only [Measure.restrict_univ] using ofRealL2_ae volume _] with x hx
    exact congrArg Complex.re hx
  · filter_upwards [show ofRealL2 volume
      (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N) g)
        =ᵐ[volume.restrict Set.univ] (fun x =>
          ((realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N) g) x : ℂ))
      from by simpa only [Measure.restrict_univ] using ofRealL2_ae volume _] with x hx
    exact congrArg Complex.re hx

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! On an existing weak Sobolev input, every derivative of the literal
spectral approximation is exactly the projection of that input derivative. -/

theorem bandProjectionHk_of_weakHk_component (N K : ℕ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K ℝ) (a : JetIndex 2 K) :
    (bandProjectionHk N K (univToPlane (f.val (valueIndex2 K)))).val a =
      planeToUniv (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
        (frequencyBall_neg N) (univToPlane (f.val a))) := by
  let P := realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N) (frequencyBall_neg N)
  let D : JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K ℝ :=
    WithLp.toLp 2 (fun b => planeToUniv (P (univToPlane (f.val b))))
  have hD : D ∈ planeHkGraph (E := ℝ) Set.univ K := by
    rw [mem_planeHkGraph_iff]
    intro j w i e
    have hw : HasWeakPartialDerivOn Set.univ i (f.val (lowerIndex2 j w))
        (f.val (nextIndex2 j w i)) := by
      simpa only [Real.inner_apply, one_mul, PlaneHk.toFunction, planeJetRepresentative] using
        f.toFunction.hasWeakJet j w i 1
    have hp : HasWeakPartialDerivOn Set.univ i
        (univToPlane (f.val (lowerIndex2 j w))) (univToPlane (f.val (nextIndex2 j w i))) := by
      apply hasWeakPartialDerivOn_congr_ae _ _ hw
      · simpa only [Measure.restrict_univ] using (univToPlane_ae (f.val (lowerIndex2 j w))).symm
      · simpa only [Measure.restrict_univ] using (univToPlane_ae (f.val (nextIndex2 j w i))).symm
    have hproj := realFrequencyBall_projection_hasWeakPartialDeriv N _ _ i hp
    have he : HasWeakPartialDerivOn Set.univ i
        (fun x => inner ℝ e (P (univToPlane (f.val (lowerIndex2 j w))) x))
        (fun x => inner ℝ e (P (univToPlane (f.val (nextIndex2 j w i))) x)) := by
      intro φ hs hc hsub
      simp only [Real.inner_apply, mul_assoc, integral_const_mul]
      rw [hproj φ hs hc hsub, mul_neg]
    apply hasWeakPartialDerivOn_congr_ae _ _ he
    · simpa only [Measure.restrict_univ, Function.comp_def, planeJetRepresentative, D, WithLp.ofLp_toLp] using
        (planeToUniv_ae (P (univToPlane (f.val (lowerIndex2 j w))))).symm.fun_comp (inner ℝ e)
    · simpa only [Measure.restrict_univ, Function.comp_def, planeJetRepresentative, D, WithLp.ofLp_toLp] using
        (planeToUniv_ae (P (univToPlane (f.val (nextIndex2 j w i))))).symm.fun_comp (inner ℝ e)
  have heq : bandProjectionHk N K (univToPlane (f.val (valueIndex2 K))) =
      (⟨D, hD⟩ : PlaneHk (Set.univ : Set (Vec 2)) K ℝ) := by
    apply PlaneHk.ext_value isOpen_univ
    exact bandProjectionHk_value N K _
  exact congrArg (fun h : PlaneHk (Set.univ : Set (Vec 2)) K ℝ => h.val a) heq

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier Filter
open scoped Topology FourierTransform
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Integration by parts for actual scalar weak L² derivatives on the plane,
obtained from the literal Fourier cutoffs and their strong convergence. -/

theorem bandWordReal_single_eq_projection_of_weakPartial (N : ℕ) (i : Fin 2)
    (f g : Lp ℝ 2 (volume : Measure (Vec 2)))
    (hw : HasWeakPartialDerivOn Set.univ i f g) :
    bandWordReal N (fun _ : Fin 1 => i) f =
      realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
        (frequencyBall_neg N) g := by
  change reL2 volume (bandWordComplex N (fun _ : Fin 1 => i) (ofRealL2 volume f)) =
    reL2 volume (spectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
      (ofRealL2 volume g))
  congr 1
  apply coordinateL2Equiv.injective
  rw [coordinate_bandWordComplex, coordinate_frequency_projection]
  have he : bandWordSymbol N (fun _ : Fin 1 => i) =
      bandDirectionSymbol N (coordinateVector i) := by
    funext ξ
    simp only [bandWordSymbol, bandDirectionSymbol, Fin.prod_univ_one]
  simpa only [he] using congrArg
    (fun h : Lp ℂ 2 (volume : Measure HilbertTwo) => 𝓕⁻ h)
    (band_derivative_multiplier_eq N _ _ _
      (coordinate_lineDerivOp_of_weakPartial f g i hw))

theorem weakPartial_inner (i : Fin 2)
    (f g h k : Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : HasWeakPartialDerivOn Set.univ i f g)
    (hhk : HasWeakPartialDerivOn Set.univ i h k) :
    inner ℝ g h = -inner ℝ f k := by
  have he (N : ℕ) :
      inner ℝ (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
        (frequencyBall_neg N) g) h =
      -inner ℝ f (realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
        (frequencyBall_neg N) k) := by
    rw [← bandWordReal_single_eq_projection_of_weakPartial N i f g hfg,
      ← bandWordReal_single_eq_projection_of_weakPartial N i h k hhk]
    exact bandWordReal_single_inner N i f h
  have hl := (tendsto_realFrequencyBall_projection g).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := h))
  have hr := ((tendsto_const_nhds (x := f)).inner (𝕜 := ℝ)
    (tendsto_realFrequencyBall_projection k)).neg
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun N => (he N).symm))

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Plane integration by parts for arbitrary finite Hilbert fibers and genuine weak L² derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hilbert_weakPartial_inner (i : Fin 2)
    (u du v dv : Lp E 2 (volume : Measure (Vec 2)))
    (hu : ∀ e, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (u x)) (fun x => inner ℝ e (du x)))
    (hv : ∀ e, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (v x)) (fun x => inner ℝ e (dv x))) :
    inner ℝ du v = -inner ℝ u dv := by
  rw [fiberL2_inner, fiberL2_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hu' : HasWeakPartialDerivOn Set.univ i (fiberCoordinate k u) (fiberCoordinate k du) := by
    apply hasWeakPartialDerivOn_congr_ae _ _ (hu (stdOrthonormalBasis ℝ E k))
    · simpa only [Measure.restrict_univ] using (fiberCoordinate_ae k u).symm
    · simpa only [Measure.restrict_univ] using (fiberCoordinate_ae k du).symm
  have hv' : HasWeakPartialDerivOn Set.univ i (fiberCoordinate k v) (fiberCoordinate k dv) := by
    apply hasWeakPartialDerivOn_congr_ae _ _ (hv (stdOrthonormalBasis ℝ E k))
    · simpa only [Measure.restrict_univ] using (fiberCoordinate_ae k v).symm
    · simpa only [Measure.restrict_univ] using (fiberCoordinate_ae k dv).symm
  exact weakPartial_inner i _ _ _ _ hu' hv'

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Every literal cutoff derivative remains in the actual spectral range.
These identities make the ambient-L² projected evolution range invariant. -/

theorem bandProjectionHk_projection (N K : ℕ)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandProjectionHk N K (realSpectralProjection (frequencyBall N)
      (frequencyBall_measurableSet N) (frequencyBall_neg N) f) =
      bandProjectionHk N K f := by
  apply PlaneHk.ext_value isOpen_univ
  rw [bandProjectionHk_value, bandProjectionHk_value, realSpectralProjection_idempotent]

theorem bandWordReal_projection (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N w (realSpectralProjection (frequencyBall N)
      (frequencyBall_measurableSet N) (frequencyBall_neg N) f) = bandWordReal N w f := by
  have h := congrArg (fun u : PlaneHk (Set.univ : Set (Vec 2)) m ℝ =>
    u.val (⟨⟨m, Nat.lt_succ_self m⟩, w⟩ : JetIndex 2 m))
      (bandProjectionHk_projection N m f)
  exact planeToUniv.injective h

theorem projection_bandWordReal (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
      (frequencyBall_neg N) (bandWordReal N w f) = bandWordReal N w f := by
  have h := bandProjectionHk_of_weakHk_component N m (bandProjectionHk N m f)
    (⟨⟨m, Nat.lt_succ_self m⟩, w⟩ : JetIndex 2 m)
  rw [bandProjectionHk_value, univToPlane_planeToUniv, bandProjectionHk_component,
    bandProjectionHk_component, univToPlane_planeToUniv, bandWordReal_projection] at h
  exact (planeToUniv.injective h).symm

theorem bandWordReal_single_comp (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N (fun _ : Fin 1 => i) (bandWordReal N w f) =
      bandWordReal N (Fin.snoc w i) f := by
  rw [bandWordReal_single_eq_projection_of_weakPartial N i _ _
    (bandWordReal_hasWeakPartialDeriv N w i f), projection_bandWordReal]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Commutation of genuine cutoff derivatives, derived from their literal
Fourier symbols. This supplies arbitrary-order projected PDE pairings. -/

/-- The last two genuine cutoff derivatives commute. -/
theorem bandWordReal_snoc_snoc_comm (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (i j : Fin 2) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N (Fin.snoc (Fin.snoc w i) j) f =
      bandWordReal N (Fin.snoc (Fin.snoc w j) i) f := by
  have hs : bandWordSymbol N (Fin.snoc (Fin.snoc w i) j) =
      bandWordSymbol N (Fin.snoc (Fin.snoc w j) i) := by
    funext ξ
    simp only [bandWordSymbol_snoc]
    ring
  simp only [bandWordReal, bandWordComplex, hs]

/-- Two single coordinate cutoff derivatives commute on every L² input. -/
theorem bandWordReal_single_single_comm (N : ℕ) (i j : Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N (fun _ : Fin 1 => i) (bandWordReal N (fun _ : Fin 1 => j) f) =
      bandWordReal N (fun _ : Fin 1 => j) (bandWordReal N (fun _ : Fin 1 => i) f) := by
  have hw (k : Fin 2) : (fun _ : Fin 1 => k) = Fin.snoc Fin.elim0 k := by
    funext a
    have ha : a = Fin.last 0 := Subsingleton.elim _ _
    subst a
    simp only [Fin.snoc_last]
  rw [bandWordReal_single_comp, bandWordReal_single_comp, hw i, hw j]
  exact bandWordReal_snoc_snoc_comm N Fin.elim0 j i f

/-- A derivative of arbitrary order commutes with a coordinate cutoff derivative.
Neither smooth input nor a separate spectral-range premise is required. -/
theorem bandWordReal_comm_single (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (i : Fin 2) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N w (bandWordReal N (fun _ : Fin 1 => i) f) =
      bandWordReal N (fun _ : Fin 1 => i) (bandWordReal N w f) := by
  induction m with
  | zero =>
    rw [bandWordReal_zero, bandWordReal_zero,
      projection_bandWordReal, bandWordReal_projection]
  | succ m ih =>
    let v : Fin m → Fin 2 := Fin.init w
    let j : Fin 2 := w (Fin.last m)
    have hw : Fin.snoc v j = w := Fin.snoc_init_self w
    rw [← hw]
    calc
      _ = bandWordReal N (fun _ : Fin 1 => j)
          (bandWordReal N v (bandWordReal N (fun _ : Fin 1 => i) f)) :=
        (bandWordReal_single_comp N v j _).symm
      _ = bandWordReal N (fun _ : Fin 1 => j)
          (bandWordReal N (fun _ : Fin 1 => i) (bandWordReal N v f)) :=
        congrArg (bandWordReal N (fun _ : Fin 1 => j)) (ih v)
      _ = bandWordReal N (fun _ : Fin 1 => i)
          (bandWordReal N (fun _ : Fin 1 => j) (bandWordReal N v f)) :=
        bandWordReal_single_single_comm N j i _
      _ = _ := congrArg (bandWordReal N (fun _ : Fin 1 => i))
        (bandWordReal_single_comp N v j f)

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Fiber coordinates reduce commutation with existing plane weak jets to the scalar proof. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The scalar graph obtained by taking one fixed fiber coordinate. -/
def coordinatePlaneHk {K : ℕ} (u : PlaneHk Set.univ K E)
    (k : Fin (Module.finrank ℝ E)) : PlaneHk Set.univ K ℝ :=
  mapPlaneHk (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E k)) u

theorem coordinatePlaneHk_component {K : ℕ} (u : PlaneHk Set.univ K E)
    (k : Fin (Module.finrank ℝ E)) (a : JetIndex2 K) :
    univToPlane ((coordinatePlaneHk u k).val a) =
      fiberCoordinate k (univToPlane (u.val a)) := by
  rw [coordinatePlaneHk, mapPlaneHk_component]
  apply Lp.ext
  have hc := ContinuousLinearMap.coeFn_compLpL
    (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E k)) (u.val a)
  simp only [Measure.restrict_univ] at hc
  filter_upwards [hc, univToPlane_ae
    ((InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E k)).compLpL 2
      (volume.restrict Set.univ) (u.val a)), fiberCoordinate_ae k (univToPlane (u.val a)),
    univToPlane_ae (u.val a)] with x hx ht he hv
  rw [ht, hx, he, hv]
  rfl

theorem hilbertBandHk_of_planeHk_component (N : ℕ) {K : ℕ}
    (u : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (hilbertBandHk N K (univToPlane (u.val (valueIndex2 K)))).val a =
      planeToUniv (hilbertProjection N (univToPlane (u.val a))) := by
  rw [hilbertBandHk_component]
  congr 1
  apply fiberCoordinate_ext
  intro k
  rw [hilbertLift_coordinate, hilbertProjection_coordinate]
  have h := bandProjectionHk_of_weakHk_component N K (coordinatePlaneHk u k) a
  rw [bandProjectionHk_component] at h
  have hp := congrArg (univToPlane (E := ℝ)) h
  simp only [univToPlane_planeToUniv, coordinatePlaneHk_component] at hp
  exact hp

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Contractive strong approximation in every actual finite-order plane
Sobolev space, by the same real spectral cutoffs used for the PDE. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbertBandHk_component_norm_le (N K : ℕ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) (a : JetIndex 2 K) :
    ‖(hilbertBandHk N K (univToPlane (f.val (valueIndex2 K)))).val a‖ ≤ ‖f.val a‖ := by
  rw [hilbertBandHk_of_planeHk_component, planeToUniv.norm_map]
  exact (hilbertProjection_norm_le N _).trans_eq (univToPlane.norm_map _)

theorem hilbertBandHk_factorialNormSq_le (N K : ℕ) (ρ : ℝ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) :
    factorialNormSq ρ (hilbertBandHk N K (univToPlane (f.val (valueIndex2 K)))).val ≤
      factorialNormSq ρ f.val := by
  unfold factorialNormSq derivativeNormSq
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ j.val)
  apply Finset.sum_le_sum
  intro w _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (hilbertBandHk_component_norm_le N K f ⟨j, w⟩)

theorem tendsto_hilbertBandHk_component (K : ℕ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) (a : JetIndex 2 K) :
    Tendsto (fun N => (hilbertBandHk N K (univToPlane (f.val (valueIndex2 K)))).val a)
      atTop (𝓝 (f.val a)) := by
  simp_rw [hilbertBandHk_of_planeHk_component]
  have h := (planeToUniv.continuous.tendsto (univToPlane (f.val a))).comp
    (tendsto_hilbertProjection (univToPlane (f.val a)))
  simpa only [planeToUniv_univToPlane, Function.comp_def] using h

theorem tendsto_hilbertBandHk (K : ℕ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) :
    Tendsto (fun N => hilbertBandHk N K (univToPlane (f.val (valueIndex2 K))))
      atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  have hc : Tendsto (fun N => fun a : JetIndex 2 K =>
      (hilbertBandHk N K (univToPlane (f.val (valueIndex2 K)))).val a)
      atTop (𝓝 (fun a => f.val a)) :=
    tendsto_pi_nhds.mpr (tendsto_hilbertBandHk_component K f)
  have h := (PiLp.continuous_toLp 2
    (fun _ : JetIndex 2 K => ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E)).tendsto
      (fun a => f.val a) |>.comp hc
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using h

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Hilbert-valued bounded Fourier derivatives and their exact energy pairings. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual cutoff derivative, lifted coordinatewise in the finite Hilbert fiber. -/
def hilbertWordOperator (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  hilbertLift (bandWordRealOperator N w)

theorem hilbertWordOperator_coordinate (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) (k : Fin (Module.finrank ℝ E)) :
    fiberCoordinate k (hilbertWordOperator N w u) =
      bandWordRealOperator N w (fiberCoordinate k u) := hilbertLift_coordinate _ _ _

theorem hilbertWord_single_comp (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N (fun _ : Fin 1 => i) (hilbertWordOperator N w u) =
      hilbertWordOperator N (Fin.snoc w i) u := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertWordOperator_coordinate, bandWordRealOperator_apply]
  exact bandWordReal_single_comp N w i _

theorem hilbertWord_comm_single (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w (hilbertWordOperator N (fun _ : Fin 1 => i) u) =
      hilbertWordOperator N (fun _ : Fin 1 => i) (hilbertWordOperator N w u) := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertWordOperator_coordinate, bandWordRealOperator_apply]
  exact bandWordReal_comm_single N w i _

theorem hilbertWord_single_inner (N : ℕ) (i : Fin 2)
    (u v : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (hilbertWordOperator N (fun _ : Fin 1 => i) u) v =
      -inner ℝ u (hilbertWordOperator N (fun _ : Fin 1 => i) v) := by
  rw [fiberL2_inner, fiberL2_inner]
  simp only [hilbertWordOperator_coordinate, bandWordRealOperator_apply,
    bandWordReal_single_inner, Finset.sum_neg_distrib]

theorem hilbertWord_second_inner_self (N : ℕ) (i : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (hilbertWordOperator N (Fin.snoc (fun _ : Fin 1 => i) i) u) u =
      -‖hilbertWordOperator N (fun _ : Fin 1 => i) u‖ ^ 2 := by
  rw [← hilbertWord_single_comp, hilbertWord_single_inner, real_inner_self_eq_norm_sq]
end

/-! Prefix jets and snoc jets agree for the genuine Fourier derivatives. -/

section
theorem bandWordSymbol_prefix_single (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2) :
    bandWordSymbol N (Fin.append (fun _ : Fin 1 => i) w) =
      bandWordSymbol N (Fin.snoc w i) := by
  funext ξ
  by_cases hξ : ξ ∈ angularBand N
  · simp only [bandWordSymbol, Set.indicator_of_mem hξ]
    rw [Fin.prod_univ_add]
    conv_rhs => rw [Fin.prod_univ_castSucc]
    simp only [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last]
    simp only [Fin.prod_univ_one]
    exact mul_comm _ _
  · simp only [bandWordSymbol, Set.indicator_of_notMem hξ]

theorem bandWordReal_prefix_single (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (u : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N (Fin.append (fun _ : Fin 1 => i) w) u =
      bandWordReal N (Fin.snoc w i) u := by
  simp only [bandWordReal, bandWordComplex, bandWordSymbol_prefix_single]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hilbertWord_prefix_single (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N (Fin.append (fun _ : Fin 1 => i) w) u =
      hilbertWordOperator N (Fin.snoc w i) u := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertWordOperator_coordinate, bandWordRealOperator_apply]
  exact bandWordReal_prefix_single N w i _
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Genuine contractive spectral cutoffs converge strongly in plane Sobolev Bochner spaces. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeHkCutoff (N K : ℕ) : PlaneHk Set.univ K E →L[ℝ] PlaneHk Set.univ K E :=
  (hilbertBandHkOperator (E := E) N K).comp (planeHkValueOperator (E := E) K)

theorem planeHkCutoff_norm_le (N K : ℕ) (u : PlaneHk Set.univ K E) :
    ‖planeHkCutoff N K u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(hilbertBandHk N K (planeHkValueOperator K u)).val‖ ^ 2 ≤ ‖u.val‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro α _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (hilbertBandHk_component_norm_le N K u α)

theorem tendsto_planeHkCutoff (K : ℕ) (u : PlaneHk Set.univ K E) :
    Tendsto (fun N => planeHkCutoff N K u) atTop (𝓝 u) :=
  tendsto_hilbertBandHk K u

theorem tendsto_planeHkCutoff_time {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ℕ) (U : Lp (PlaneHk Set.univ K E) 2 μ) :
    Tendsto (fun N => (planeHkCutoff (E := E) N K).compLpL 2 μ U) atTop (𝓝 U) :=
  contractiveApproximation_time_tendsto μ (fun N => planeHkCutoff (E := E) N K)
    (fun N u => planeHkCutoff_norm_le N K u) (tendsto_planeHkCutoff K) U

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Actual Fourier cutoffs and their ordered derivatives commute with fixed fiber maps. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem hilbertWord_fiberMap (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (L : E →L[ℝ] F) (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w (L.compLpL 2 volume u) =
      L.compLpL 2 volume (hilbertWordOperator N w u) :=
  hilbertLift_fiberMap _ L u

theorem hilbertProjection_fiberMap (N : ℕ) (L : E →L[ℝ] F)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertProjection N (L.compLpL 2 volume u) =
      L.compLpL 2 volume (hilbertProjection N u) :=
  hilbertLift_fiberMap _ L u

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! A further plane Fourier cutoff contracts the genuine Sobolev norm of a range element. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbertBandHk_norm_le_of_range (M N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) (hu : hilbertProjection N u = u) :
    ‖hilbertBandHk M K u‖ ≤ ‖hilbertBandHk N K u‖ := by
  have he := planeHkCutoff_norm_le M K (hilbertBandHk N K u)
  simpa only [planeHkCutoff, ContinuousLinearMap.comp_apply, hilbertBandHkOperator_apply,
    planeHkValueOperator_apply, hilbertBandHk_value, univToPlane_planeToUniv, hu] using he
end

/-! Each cutoff derivative of a true Sobolev value is the cutoff of its corresponding weak jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbertWord_planeHk_value (N : ℕ) {K : ℕ}
    (u : PlaneHk Set.univ K E) (α : JetIndex2 K) :
    hilbertWordOperator N α.2 (planeHkValueOperator K u) =
      hilbertProjection N (univToPlane (u.val α)) := by
  have he := hilbertBandHk_of_planeHk_component N u α
  rw [hilbertBandHk_component] at he
  have h := congrArg (univToPlane (E := E)) he
  simpa only [univToPlane_planeToUniv, planeHkValueOperator_apply,
    hilbertWordOperator] using h
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Literal Fourier derivative tensors, divergence and Laplacian on plane Hilbert fibers. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The complete ordered derivative tensor of the actual cutoff. -/
def bandTensorOperator (N r : ℕ) : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
    Lp (PiLp 2 (fun _ : DerivativeWord2 r => E)) 2 (volume : Measure (Vec 2)) :=
  ∑ w : DerivativeWord2 r, ((tensorEntryCLM (J := DerivativeWord2 r) (E := E) w).compLpL 2 volume).comp
    (hilbertWordOperator (E := E) N w)

/-- The actual two-direction gradient of the cutoff, in the flux fiber of
`coupled_energy_plane`. -/
def bandGradientOperator (N : ℕ) : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
    Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)) :=
  ∑ k : Fin 2, ((tensorEntryCLM (J := Fin 2) (E := E) k).compLpL 2 volume).comp
    (hilbertWordOperator (E := E) N (fun _ : Fin 1 => k))

/-- The actual divergence after applying the frequency cutoff to a vector flux. -/
def bandDivergenceOperator (N : ℕ) :
    Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2)) :=
  ∑ i : Fin 2, (hilbertWordOperator N (fun _ : Fin 1 => i)).comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) i).compLpL 2 volume)

/-- The actual Laplacian of the frequency cutoff. -/
def bandLaplacianOperator (N : ℕ) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  ∑ i : Fin 2, hilbertWordOperator N (Fin.snoc (fun _ : Fin 1 => i) i)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandLaplacianOperator_inner_self (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (bandLaplacianOperator N u) u =
      -(∑ i : Fin 2, ‖hilbertWordOperator N (fun _ : Fin 1 => i) u‖ ^ 2) := by
  simp only [bandLaplacianOperator, sum_apply, sum_inner,
    hilbertWord_second_inner_self, Finset.sum_neg_distrib]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandTensorOperator_ae (N r : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    bandTensorOperator (E := E) N r u =ᵐ[volume] fun x =>
      (WithLp.toLp 2 (fun w : DerivativeWord2 r => hilbertWordOperator (E := E) N w u x) :
        PiLp 2 (fun _ : DerivativeWord2 r => E)) := by
  classical
  simp only [bandTensorOperator, sum_apply, ContinuousLinearMap.comp_apply]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun w : DerivativeWord2 r =>
    (tensorEntryCLM (J := DerivativeWord2 r) (E := E) w).compLpL 2 volume (hilbertWordOperator (E := E) N w u))
  have ht := ae_all_iff.mpr (fun w : DerivativeWord2 r =>
    ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := DerivativeWord2 r) (E := E) w) (hilbertWordOperator (E := E) N w u))
  filter_upwards [hs, ht] with x hx hh
  rw [hx, Finset.sum_apply]
  apply PiLp.ext
  intro w
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hh]
  change (∑ k : DerivativeWord2 r, PiLp.single 2 k (hilbertWordOperator N k u x) w) = _
  simp
end

/-! Exact adjoint pairing of the actual plane cutoff gradient and divergence. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Fiber tensor injection and projection are adjoints also in spatial L². -/
theorem tensorEntryLp_inner (i : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2)))
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    inner ℝ ((tensorEntryCLM (J := Fin 2) (E := E) i).compLpL 2 volume u) F =
      inner ℝ u ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) i).compLpL 2 volume F) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := Fin 2) (E := E) i) u,
    ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) i) F] with x hu hF
  rw [hu, hF]
  change inner ℝ (PiLp.single (β := fun _ : Fin 2 => E) 2 i (u x)) (F x) =
    inner ℝ (u x) (F x i)
  rw [PiLp.inner_apply]
  simp only [PiLp.ofLp_single, Pi.single_apply]
  change (∑ k : Fin 2, inner ℝ (if k = i then u x else 0) (F x k)) = _
  have hi (k : Fin 2) : inner ℝ (if k = i then u x else 0) (F x k) =
      if k = i then inner ℝ (u x) (F x i) else 0 := by
    by_cases hki : k = i <;> simp [hki]
  simp_rw [hi]
  simp

theorem bandDivergence_gradient_inner (N : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2)))
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    inner ℝ (bandDivergenceOperator (E := E) N F) u =
      -inner ℝ F (bandGradientOperator (E := E) N u) := by
  simp only [bandDivergenceOperator, bandGradientOperator, sum_apply,
    ContinuousLinearMap.comp_apply, sum_inner, inner_sum, hilbertWord_single_inner,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa only [real_inner_comm] using
    (tensorEntryLp_inner i (hilbertWordOperator N (fun _ : Fin 1 => i) u) F).symm
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Actual projected derivatives remain in the same frequency range. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hilbertProjection_word (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertProjection N (hilbertWordOperator N w u) = hilbertWordOperator N w u := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertProjection_coordinate, hilbertWordOperator_coordinate, bandWordRealOperator_apply]
  exact projection_bandWordReal N w _

theorem hilbertWord_projection (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w (hilbertProjection N u) = hilbertWordOperator N w u := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertProjection_coordinate, hilbertWordOperator_coordinate, bandWordRealOperator_apply]
  exact bandWordReal_projection N w _

theorem hilbertProjection_laplacian (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertProjection N (bandLaplacianOperator N u) = bandLaplacianOperator N u := by
  simp only [bandLaplacianOperator, sum_apply, map_sum, hilbertProjection_word]

theorem hilbertProjection_divergence (N : ℕ)
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    hilbertProjection N (bandDivergenceOperator (E := E) N F) = bandDivergenceOperator (E := E) N F := by
  simp only [bandDivergenceOperator, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, hilbertProjection_word]
end

/-! Exact commutation and differentiated energy pairings for the plane cutoff differential operators. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hilbertWord_laplacian (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w (bandLaplacianOperator N u) =
      bandLaplacianOperator N (hilbertWordOperator N w u) := by
  simp only [bandLaplacianOperator, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hilbertWord_single_comp, hilbertWord_comm_single, hilbertWord_comm_single,
    hilbertWord_single_comp]

theorem hilbertWord_divergence (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w (bandDivergenceOperator (E := E) N F) =
      bandDivergenceOperator (E := E) N (hilbertWordOperator N w F) := by
  simp only [bandDivergenceOperator, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hilbertWord_comm_single, hilbertWord_fiberMap]

theorem hilbertWord_laplacian_inner (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (hilbertWordOperator N w (bandLaplacianOperator N u))
      (hilbertWordOperator N w u) =
      -(∑ i : Fin 2, ‖hilbertWordOperator N (fun _ : Fin 1 => i)
        (hilbertWordOperator N w u)‖ ^ 2) := by
  rw [hilbertWord_laplacian, bandLaplacianOperator_inner_self]

theorem hilbertWord_divergence_inner (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2)))
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    inner ℝ (hilbertWordOperator N w (bandDivergenceOperator (E := E) N F))
      (hilbertWordOperator N w u) =
      -inner ℝ (hilbertWordOperator N w F)
        (bandGradientOperator (E := E) N (hilbertWordOperator N w u)) := by
  rw [hilbertWord_divergence, bandDivergence_gradient_inner]
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Testing against an actual cutoff jet removes the projection from a genuine Sobolev product. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbertBandHk_projection (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertBandHk N K (hilbertProjection N u) = hilbertBandHk N K u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  simp only [hilbertBandHk_component]
  change planeToUniv (hilbertWordOperator N α.2 (hilbertProjection N u)) =
    planeToUniv (hilbertWordOperator N α.2 u)
  rw [hilbertWord_projection]

theorem hilbertBandHk_carrier_factorialPairing (N K : ℕ) (ρ : ℝ)
    (q : PlaneHk Set.univ K E) (u : Lp E 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ (hilbertBandHk N K (planeHkValueOperator K q)).val
      (hilbertBandHk N K u).val = factorialPairing ρ q.val (hilbertBandHk N K u).val := by
  unfold factorialPairing
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [hilbertBandHk_component, hilbertBandHk_component]
  change inner ℝ (planeToUniv (hilbertWordOperator N w (planeHkValueOperator K q)))
    (planeToUniv (hilbertWordOperator N w u)) = _
  rw [hilbertWord_planeHk_value N q ⟨j, w⟩, planeToUniv_inner,
    hilbertProjection_inner, hilbertProjection_word]
  have he := planeToUniv_inner (univToPlane (q.val ⟨j, w⟩)) (hilbertWordOperator N w u)
  rw [planeToUniv_univToPlane] at he
  exact he.symm

end AVRegularity.CoupledEnergyPlane.Fourier
end
