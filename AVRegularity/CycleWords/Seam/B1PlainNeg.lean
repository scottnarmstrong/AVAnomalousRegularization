-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.OldAdjointIdentification
import AVRegularity.CycleWords.FibreGraphNativeSeries
public import AVRegularity.CycleWords.Seam.Leibniz
public import AVRegularity.CycleWords.MixedWords.Discard.Pair

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords.Seam

/-! **Vector duality of a word-chain level with the reversed adjoint chain.** A test family
`Φ_x ∈ H^m(ℝ², h_x)` is split in orthonormal coordinates; each coordinate runs the scalar reversed
chain `ψ_{x,e}` of the metric `G(-τ)` and the drift `-v(-τ)`, and the vector adjoint is
`Ψ_x = ∑_e ψ_{x,e} b_e` (`planeHkAssemble`). For a level whose previous-letter flux has an `L²`
realization `S`:

`∑_x π_x⁻¹ ⟨u_x(b), Φ_x⟩ = ∑_x π_x⁻¹ ⟨f_x, Ψ_x(a)⟩ - ∫_a^b ∑_x π_x⁻¹ ⟨S_x(r), ∇Ψ_x(r)⟩ dr`.

At level `0` the flux is zero; at level `j + 1` it is the letter flux of level `j`. -/

section
/-- A pairing of an `L²`-in-time field with a continuous one is integrable on a compact window. -/
theorem intervalIntegrable_inner_memLp_continuousOn {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] {a b : ℝ} (hab : a ≤ b) {A B : ℝ → X}
    (hA : MemLp A 2 (volume.restrict (Icc a b))) (hB : ContinuousOn B (Icc a b)) :
    IntervalIntegrable (fun r => inner ℝ (A r) (B r)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  have hA1 : Integrable A (volume.restrict (Icc a b)) := hA.integrable (by norm_num)
  refine Integrable.mono' (hA1.norm.const_mul C) ?_ ?_
  · exact hA.aestronglyMeasurable.inner (hB.aestronglyMeasurable measurableSet_Icc)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    calc ‖inner ℝ (A r) (B r)‖ ≤ ‖A r‖ * ‖B r‖ := norm_inner_le_norm _ _
      _ ≤ C * ‖A r‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hC r hr) (norm_nonneg _)

section Readouts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkValueOperator_eq_planeJetL2 {K : ℕ} (u : PlaneHk Set.univ K E) :
    planeHkValueOperator K u = planeJetL2 u (valueIndex2 K) := rfl

theorem planeH1Gradient_truncate_eq {m : ℕ} (hm : 1 ≤ m) (u : PlaneHk Set.univ m E) (k : Fin 2) :
    planeH1GradientOperator (truncatePlaneHk hm u) k =
      planeJetL2 u (truncateJetIndex hm ⟨⟨1, by omega⟩, fun _ => k⟩) := rfl

/-- The flux pairing with the gradient of an assembled field splits over the coordinates. -/
theorem flux_inner_gradient_assemble {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E)
    {m : ℕ} (hm : 1 ≤ m) (S : PlaneFluxL2 E) (ψ : n → PlaneHk Set.univ m ℝ) :
    ∑ e, inner ℝ (planeFluxFiberCoordinateCLM (B e) S)
        (planeH1GradientOperator (truncatePlaneHk hm (ψ e))) =
      inner ℝ S (planeH1GradientOperator (truncatePlaneHk hm (planeHkAssemble B ψ))) := by
  simp only [PiLp.inner_apply, planeH1Gradient_truncate_eq, planeJetL2_assemble, inner_assemble,
    planeFluxFiberCoordinateCLM_apply]
  exact Finset.sum_comm

theorem continuousOn_planeHkAssemble {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E)
    {m : ℕ} {s : Set ℝ} (ψ : n → ℝ → PlaneHk Set.univ m ℝ) (hψ : ∀ e, ContinuousOn (ψ e) s) :
    ContinuousOn (fun τ => planeHkAssemble B (fun e => ψ e τ)) s := by
  unfold planeHkAssemble
  simp_rw [← mapPlaneHkOperator_apply]
  exact continuousOn_finsetSum _ fun e _ =>
    (mapPlaneHkOperator m ((ContinuousLinearMap.id ℝ ℝ).smulRight (B e))).continuous.comp_continuousOn
      (hψ e)

end Readouts

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- The reversed chain on `[-b, -a]` is continuous at reflected times. -/
theorem reversedChain_gradient_continuousOn {m : ℕ} (hm : 1 ≤ m) {a b : ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (Ψ : ℝ → PlaneHk Set.univ m E) (hΨ : ContinuousOn Ψ (Icc (-b) (-a))) :
    ContinuousOn (fun r => planeH1GradientOperator (truncatePlaneHk hm (Ψ (-r)))) (Icc a b) :=
  (planeH1GradientOperator.continuous.comp (truncatePlaneHk hm).continuous).comp_continuousOn
    (hΨ.comp continuous_neg.continuousOn fun _ hr => ⟨neg_le_neg hr.2, neg_le_neg hr.1⟩)

/-- **Coordinate duality with the reversed chain, `L²` flux form.** -/
theorem wordChain_component_reversedChain_native_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι)
    (S : ℝ → PlaneFluxL2 (h i.2)) (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S r k =ᵐ[volume]
      fun x => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r x k)
    (e : h i.2) (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw) :
    inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i b)))
        (planeHkValueOperator m (g ())) =
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i)))
          (planeHkValueOperator m (ψ 0 () (-a))) -
        ∫ r in a..b, inner ℝ (planeFluxFiberCoordinateCLM e (S r))
          (planeH1GradientOperator (truncatePlaneHk hm (ψ 0 () (-r)))) := by
  obtain ⟨Cr, hCrpos, hCr⟩ := cellDriftTorusSymbol_bound _ (cellDrift_timeReverse hv)
  have hd := wordChainCoordinateNative_duhamel hD G hG letters X0 δ κ a b hab v hv M hb f U Uw
    hsol i S hSl hS e (planeHkValueOperator m (g ()))
  dsimp only at hd
  rw [hd, backwardField_trace_eq_reversedChain hab G hG v hv M hb Cr hCrpos hCr m g ψ ψw hψ
    ⟨-a, ⟨neg_le_neg hab, le_rfl⟩⟩]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [backwardField_h1State_eq_reversedChain_neg hab G hG v hv M hb Cr hCrpos hCr m hm
    g ψ ψw hψ] with r hr hmem
  rw [Set.uIoc_of_le hab] at hmem
  rw [hr ⟨hmem.1.le, hmem.2⟩]

/-- **Vector duality of one component with the assembled reversed chain.** -/
theorem wordChain_component_vector_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι)
    (S : ℝ → PlaneFluxL2 (h i.2)) (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S r k =ᵐ[volume]
      fun x => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r x k)
    {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ (h i.2))
    (m : ℕ) (hm : 1 ≤ m) (Φ : PlaneHk Set.univ m (h i.2))
    (ψ : n → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : n → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : ∀ e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B e) Φ) (fun _ _ _ => 0) (ψ e) (ψw e)) :
    inner ℝ (planeHkValueOperator (κ i.1 i.2) (U i b)) (planeHkValueOperator m Φ) =
      inner ℝ (planeHkValueOperator (κ i.1 i.2) (f i))
          (planeHkValueOperator m (planeHkAssemble B (fun e => ψ e 0 () (-a)))) -
        ∫ r in a..b, inner ℝ (S r)
          (planeH1GradientOperator (truncatePlaneHk hm
            (planeHkAssemble B (fun e => ψ e 0 () (-r))))) := by
  have hcomp := fun e => wordChain_component_reversedChain_native_duality hD G hG letters X0 δ κ
    a b hab v hv M hb f U Uw hsol i S hSl hS (B e) m hm (fun _ => planeHkCoord (B e) Φ) (ψ e)
    (ψw e) (hψ e)
  have hint : ∀ e, IntervalIntegrable (fun r => inner ℝ (planeFluxFiberCoordinateCLM (B e) (S r))
      (planeH1GradientOperator (truncatePlaneHk hm (ψ e 0 () (-r))))) volume a b := fun e =>
    intervalIntegrable_inner_memLp_continuousOn hab
      ((planeFluxFiberCoordinateCLM (B e)).comp_memLp' hSl)
      (reversedChain_gradient_continuousOn hm (ψ e 0 ()) ((hψ e).1 ((0 : Fin 1), ())))
  rw [inner_eq_sum_planeFiberCoordinate B]
  simp only [planeHkValueOperator_eq_planeJetL2, planeJetL2_assemble, inner_assemble]
  simp only [planeHkValueOperator_eq_planeJetL2, planeJetL2_coord] at hcomp
  rw [Finset.sum_congr rfl fun e _ => hcomp e, Finset.sum_sub_distrib,
    ← intervalIntegral.integral_finsetSum fun e _ => hint e]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  exact flux_inner_gradient_assemble B hm (S r) (fun e => ψ e 0 () (-r))

/-- **Vector duality of a word-chain level**, inverse-mass weighted. -/
theorem wordChain_level_vector_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (l : Fin (N + 1))
    (S : ∀ x, ℝ → PlaneFluxL2 (h x)) (hSl : ∀ x, MemLp (S x) 2 (volume.restrict (Icc a b)))
    (hS : ∀ x, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S x r k =ᵐ[volume]
      fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (l, x) r z k)
    (π : ι → ℝ) {n : ι → Type*} [∀ x, Fintype (n x)] (B : ∀ x, OrthonormalBasis (n x) ℝ (h x))
    (m : ℕ) (hm : 1 ≤ m) (Φ : ∀ x, PlaneHk Set.univ m (h x))
    (ψ : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : ∀ x e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B x e) (Φ x)) (fun _ _ _ => 0)
      (ψ x e) (ψw x e)) :
    ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ l x) (U (l, x) b))
        (planeHkValueOperator m (Φ x)) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ l x) (f (l, x)))
          (planeHkValueOperator m (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) -
        ∫ r in a..b, ∑ x, (π x)⁻¹ * inner ℝ (S x r)
          (planeH1GradientOperator (truncatePlaneHk hm
            (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))))) := by
  have hx := fun x => wordChain_component_vector_duality hD G hG letters X0 δ κ a b hab v hv M hb
    f U Uw hsol (l, x) (S x) (hSl x) (hS x) (B x) m hm (Φ x) (ψ x) (ψw x) (hψ x)
  have hint : ∀ x, IntervalIntegrable (fun r => (π x)⁻¹ * inner ℝ (S x r)
      (planeH1GradientOperator (truncatePlaneHk hm
        (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r)))))) volume a b := fun x =>
    (intervalIntegrable_inner_memLp_continuousOn hab (hSl x)
      (reversedChain_gradient_continuousOn hm _
        (continuousOn_planeHkAssemble (B x) (fun e => ψ x e 0 ())
          fun e => (hψ x e).1 ((0 : Fin 1), ())))).const_mul _
  rw [intervalIntegral.integral_finsetSum fun x _ => hint x, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intervalIntegral.integral_const_mul, ← mul_sub]
  exact congrArg (fun y => (π x)⁻¹ * y) (hx x)
end

/-! **The step of the adjoint word chain.** For the level `j + 1` of a word chain on `[a, b]` and a
test family `Φ ∈ H^{n+d}`, with `Ψ` the assembled reversed chain from `Φ`:

`⟨u_{j+1}(b), Φ⟩_π = ⟨f_{j+1}, Ψ(a)⟩_π - ∫_a^b ⟨u_j(r), L_j^* Ψ(r)⟩_π dr`,

where `L_j^*` is the transposed letter (`letterTransposeJet`) of the `j`-th letter, of order `d`.
At level `0` there is no letter: `⟨u_0(b), Φ⟩_π = ⟨f_0, Ψ(a)⟩_π`. -/

section
section Pairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The flux pairing with the gradient of a test, as an integral of jets. -/
theorem flux_inner_gradient_integral (S : PlaneFluxL2 E) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hS : ∀ k, S k =ᵐ[volume] fun z => F z k) {m : ℕ} (hm : 1 ≤ m)
    (Ψ : PlaneHk Set.univ m E) :
    inner ℝ S (planeH1GradientOperator (truncatePlaneHk hm Ψ)) =
      ∫ z, ∑ k : Fin 2, inner ℝ (F z k) (Ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
  have hae : ∀ k, (fun z => inner ℝ (S k z)
      (planeJetL2 Ψ (truncateJetIndex hm ⟨⟨1, by omega⟩, fun _ => k⟩) z)) =ᵐ[volume]
      fun z => inner ℝ (F z k) (Ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
    intro k
    filter_upwards [hS k, planeJetL2_ae Ψ (truncateJetIndex hm ⟨⟨1, by omega⟩, fun _ => k⟩)]
      with z h1 h2
    rw [h1, h2]
    rfl
  have hint : ∀ k, Integrable (fun z => inner ℝ (F z k)
      (Ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z)) volume := fun k =>
    (L2.integrable_inner (S k) (planeJetL2 Ψ (truncateJetIndex hm ⟨⟨1, by omega⟩, fun _ => k⟩))).congr
      (hae k)
  rw [integral_finsetSum _ fun k _ => hint k, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [planeH1Gradient_truncate_eq, L2.inner_def]
  exact integral_congr_ae (hae k)

end Pairing

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- **The step of the adjoint word chain**: level `j + 1` against a test, through the transposed
`j`-th letter applied to the assembled reversed chain. -/
theorem wordChain_letter_step_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (j : Fin N)
    (S : ∀ x, ℝ → PlaneFluxL2 (h x)) (hSl : ∀ x, MemLp (S x) 2 (volume.restrict (Icc a b)))
    (hS : ∀ x, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S x r k =ᵐ[volume]
      fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (j.succ, x) r z k)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    {n : ι → Type*} [∀ x, Fintype (n x)] (B : ∀ x, OrthonormalBasis (n x) ℝ (h x))
    (m d : ℕ) (hd : 1 ≤ d)
    (hempty : ∀ x u (o : Finset.Icc 2 D), d < o.1 → (letters j).edge x u o = [])
    (Φ : ∀ x, PlaneHk Set.univ (m + d) (h x))
    (ψ : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + d) ℝ)
    (ψw : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + d + 1) ℝ)
    (hψ : ∀ x e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m + d)
      (-b) (-a) (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B x e) (Φ x))
      (fun _ _ _ => 0) (ψ x e) (ψw x e))
    (hreg : ∀ᵐ r ∂volume.restrict (Icc a b),
      LetterTermRegular (letters j) (if (letters j).positive then 1 else 0) X0 δ r m d
        (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r)))) :
    ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ j.succ x) (U (j.succ, x) b))
        (planeHkValueOperator (m + d) (Φ x)) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ j.succ x) (f (j.succ, x)))
          (planeHkValueOperator (m + d) (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) -
        ∫ r in a..b, ∑ u, (π u)⁻¹ * ∫ z,
          inner ℝ ((U (j.castSucc, u) r).toFunction.jet (valueIndex2 (κ j.castSucc u)) z)
            (letterTransposeJet π (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
              (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
              (if (letters j).positive then 1 else 0) X0 δ r m d
              (fun x => (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet) u
              (valueIndex2 m) z) := by
  have hm : 1 ≤ m + d := by omega
  refine (wordChain_level_vector_duality hD G hG letters X0 δ κ a b hab v hv M hb f U Uw hsol
    j.succ S hSl hS π B (m + d) hm Φ ψ ψw hψ).trans ?_
  congr 1
  apply intervalIntegral.integral_congr_ae
  have htr : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ u,
      truncatePlaneHk (Nat.le_succ _) (Uw (j.castSucc, u) r) = U (j.castSucc, u) r :=
    ae_all_iff.mpr fun u => hsol.2.2.1 (j.castSucc, u)
  have hall := (ae_restrict_iff' measurableSet_Icc).mp
    (htr.and ((ae_all_iff.mpr hS).and hreg))
  filter_upwards [hall] with r hr hmem
  rw [Set.uIoc_of_le hab] at hmem
  obtain ⟨htr_r, hS_r, hreg_r⟩ := hr ⟨hmem.1.le, hmem.2⟩
  calc ∑ x, (π x)⁻¹ * inner ℝ (S x r) (planeH1GradientOperator (truncatePlaneHk hm
          (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r)))))
      = ∑ x, (π x)⁻¹ * ∫ z, ∑ k : Fin 2,
          inner ℝ ((letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
            (j.succ, x) (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0)
            X0 δ (fun u => Uw (j.castSucc, u) r) r z) k)
          ((planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet
            ⟨⟨1, by omega⟩, fun _ => k⟩ z) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [flux_inner_gradient_integral (S x r) _ (hS_r x) hm]
        simp only [wordChainPreviousFlux_succ]
    _ = ∑ u, (π u)⁻¹ * ∫ z,
          inner ℝ ((Uw (j.castSucc, u) r).toFunction.jet (valueIndex2 (κ j.castSucc u + 1)) z)
            (letterTransposeJet π (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
              (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
              (if (letters j).positive then 1 else 0) X0 δ r m d
              (fun x => (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet) u
              (valueIndex2 m) z) :=
        letterTranspose_duality π hπ (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
          (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
          (if (letters j).positive then 1 else 0) X0 δ r m d hd hempty
          (fun u => Uw (j.castSucc, u) r) _ hreg_r
    _ = _ := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← htr_r u]
        rfl

/-- **Level `0` of the adjoint word chain**: no letter feeds the first level. -/
theorem wordChain_initial_vector_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (π : ι → ℝ) {n : ι → Type*} [∀ x, Fintype (n x)] (B : ∀ x, OrthonormalBasis (n x) ℝ (h x))
    (m : ℕ) (hm : 1 ≤ m) (Φ : ∀ x, PlaneHk Set.univ m (h x))
    (ψ : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : ∀ x e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B x e) (Φ x)) (fun _ _ _ => 0)
      (ψ x e) (ψw x e)) :
    ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ 0 x) (U (0, x) b))
        (planeHkValueOperator m (Φ x)) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ 0 x) (f (0, x)))
          (planeHkValueOperator m (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) := by
  have hS : ∀ x, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k,
      (0 : ℝ → PlaneFluxL2 (h x)) r k =ᵐ[volume]
        fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (0, x) r z k := by
    intro x
    refine Filter.Eventually.of_forall fun r k => ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [wordChainPreviousFlux_zero]
    simp
  refine (wordChain_level_vector_duality hD G hG letters X0 δ κ a b hab v hv M hb f U Uw hsol
    0 (fun _ => 0) (fun _ => MemLp.zero) hS π B m hm Φ ψ ψw hψ).trans ?_
  simp
end

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Seam

/-! # Quiet margin fibre bound: the plain pass with negative input

`b1_plain_pass_neg`: `plain_pass` with the stage data at the start measured by their
pairings with the tests of their order: if `|⟨W_i(a), φ⟩| ≤ X_i ‖φ‖_{H^{s_k}}` for every stage `i`
of order `k`, then every stage of order `k` tested at time `t` is at most
`C_k (1 + (t − a))^k κ(a,t) (Σ X_i²)^{1/2} ‖ψ‖`. The adjoint representatives `U_i(a)` of the plain
pass are already `H^{s_k}` tests, so only the initial term of the duality changes. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

section Pass

variable {I : Type*} [Fintype I]

/-- The initial term with negative input. -/
theorem b1_init_le (T : Finset I) {N : ℕ} (w : I → ComplexCellL2) (U : I → TorusHk N ℂ)
    (Xn : I → ℝ) (hX : ∀ i ∈ T, ‖cellComplexPair (w i) (torusHkValueCLM (U i))‖ ≤ Xn i * ‖U i‖) :
    ‖∑ i ∈ T, cellComplexPair (w i) (torusHkValueCLM (U i))‖ ≤
      Real.sqrt (∑ i, Xn i ^ 2) * Real.sqrt (∑ i ∈ T, ‖U i‖ ^ 2) := by
  calc ‖∑ i ∈ T, cellComplexPair (w i) (torusHkValueCLM (U i))‖
      ≤ ∑ i ∈ T, Xn i * ‖U i‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum hX)
    _ ≤ Real.sqrt (∑ i ∈ T, Xn i ^ 2) * Real.sqrt (∑ i ∈ T, ‖U i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ i, Xn i ^ 2) * Real.sqrt (∑ i ∈ T, ‖U i‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun i _ _ => sq_nonneg _)) (Real.sqrt_nonneg _)

/-- **The plain pass with negative input.** -/
theorem b1_plain_pass_neg (st : I → ℕ) (s : ℕ → ℕ) (M : ℕ) {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (Fl : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (Fl i t)))
    (κ : ℝ → ℝ → ℝ) (A Ca B : ℝ) (hκ : ∀ r t, 0 ≤ κ r t)
    (hmul : ∀ r t, a ≤ r → r ≤ t → t ≤ b → κ a r * κ r t ≤ A * κ a t)
    (hA : 0 ≤ A) (hCa : 0 ≤ Ca) (hB : 0 ≤ B)
    (Xn : I → ℝ)
    (hX : ∀ k < M, ∀ i, st i = k → ∀ φ : TorusHk (s k) ℂ,
      ‖cellComplexPair (W i a) (torusHkValueCLM φ)‖ ≤ Xn i * ‖φ‖)
    (hadj : ∀ k < M, ∀ t ∈ Icc a b, ∀ ψ : I → TorusHk (s k) ℂ,
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ)
        (U : I → ℝ → TorusHk (s k) ℂ),
        (∀ i, CellWeakHilbertCurve a t (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0)) ∧
        (∀ i, Ψv i t = torusHkValueCLM (ψ i)) ∧
        (∀ i, ∀ r ∈ Icc a t, torusHkValueCLM (U i r) = Ψv i r) ∧
        ∀ r ∈ Icc a t, Real.sqrt (∑ i ∈ stageSet st k, ‖U i r‖ ^ 2) ≤
          Ca * κ r t * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2))
    (hrep : ∀ k < M, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ (z : I → TorusHk 1 ℂ)
      (ψ : I → TorusHk (s k) ℂ), (∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) →
      ∃ Φ : ∀ k', I → TorusHk (s k') ℂ,
        (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ‖Φ k' i'‖ ^ 2) ≤
          B * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2)) ∧
        ∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (Fl i r) (z i) =
          ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
            cellComplexPair (W i' r) (torusHkValueCLM (Φ k' i'))) :
    ∀ k < M, ∀ t ∈ Icc a b, ∀ ψ : I → TorusHk (s k) ℂ,
      ‖∑ i ∈ stageSet st k, cellComplexPair (W i t) (torusHkValueCLM (ψ i))‖ ≤
        plainConst Ca A B k * (1 + (t - a)) ^ k * κ a t *
          Real.sqrt (∑ i, Xn i ^ 2) * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk t ht ψ
  set X := Real.sqrt (∑ i, Xn i ^ 2) with hXdef
  set Y := Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2) with hYdef
  have hXp : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  obtain ⟨Ψv, Ψs, U, hΨ, hΨt, hU, hUn⟩ := hadj k hk t ht ψ
  have hat : a ≤ t := ht.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  -- the duality, member by member
  have hF1 : ∀ i, cellComplexPair (W i t) (torusHkValueCLM (ψ i)) =
      cellComplexPair (W i a) (Ψv i a) +
        ∫ r in a..t, cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r) := by
    intro i
    have h := cellWeakAdjointPairing_forced hat C hG V hv hb ((hW i).mono hsub) (hΨ i)
    rw [hΨt i] at h
    rw [← h]
    ring
  have hint : ∀ i, IntervalIntegrable
      (fun r => cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r)) volume a t := fun i =>
    cellWeakAdjoint_forced_source_intervalIntegrable hat C hG V hv hb ((hW i).mono hsub) (hΨ i)
  have hsum : ∑ i ∈ stageSet st k, cellComplexPair (W i t) (torusHkValueCLM (ψ i)) =
      ∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a) +
        ∫ r in a..t, ∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hint i), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hF1 i
  -- the initial term, with negative input
  have haI : a ∈ Icc a t := ⟨le_rfl, hat⟩
  have hinit : ‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖ ≤
      Ca * κ a t * X * Y := by
    have hΨa : ∀ i ∈ stageSet st k, Ψv i a = torusHkValueCLM (U i a) :=
      fun i _ => (hU i a haI).symm
    rw [Finset.sum_congr rfl fun i hi => by rw [hΨa i hi]]
    refine (b1_init_le (stageSet st k) (fun i => W i a) (fun i => U i a) Xn
      (fun i hi => hX k hk i (Finset.mem_filter.1 hi).2 (U i a))).trans ?_
    calc X * Real.sqrt (∑ i ∈ stageSet st k, ‖U i a‖ ^ 2) ≤ X * (Ca * κ a t * Y) :=
          mul_le_mul_of_nonneg_left (hUn a haI) hXp
      _ = Ca * κ a t * X * Y := by ring
  -- the integral term
  set Sk := ∑ k' ∈ Finset.range k, plainConst Ca A B k' with hSk
  have hSk0 : 0 ≤ Sk := Finset.sum_nonneg fun k' _ => plainConst_nonneg hCa hA hB k'
  have hpt : ∀ᵐ r ∂volume, r ∈ Ioc a t →
      ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r)‖ ≤
        A * B * Ca * Sk * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y := by
    have h1 := (ae_restrict_iff' measurableSet_Icc).1 (hrep k hk)
    have h2 : ∀ᵐ r ∂volume, r ∈ Icc a t → ∀ i, Ψv i r = torusHkValueCLM (Ψs i r) := by
      rw [← ae_restrict_iff' measurableSet_Icc]
      exact ae_all_iff.2 fun i => (hΨ i).agrees
    filter_upwards [h1, h2] with r hr1 hr2 hr
    have hrI : r ∈ Icc a t := ⟨hr.1.le, hr.2⟩
    obtain ⟨Φ, hΦn, hΦe⟩ := hr1 (hsub hrI) (fun i => Ψs i r) (fun i => U i r)
      (fun i => by rw [← hr2 hrI i, hU i r hrI])
    rw [hΦe]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k' ∈ Finset.range k, ‖∑ i' ∈ stageSet st k',
          cellComplexPair (W i' r) (torusHkValueCLM (Φ k' i'))‖
        ≤ ∑ k' ∈ Finset.range k, A * B * Ca * plainConst Ca A B k' * (1 + (t - a)) ^ (k - 1) *
            κ a t * X * Y := by
          refine Finset.sum_le_sum fun k' hk' => ?_
          have hk'k := Finset.mem_range.1 hk'
          refine (ih k' hk'k (hk'k.trans hk) r (hsub hrI) (Φ k')).trans ?_
          have hb1 := (hΦn k' hk'k).trans
            (mul_le_mul_of_nonneg_left (hUn r hrI) hB)
          calc plainConst Ca A B k' * (1 + (r - a)) ^ k' * κ a r * X *
                Real.sqrt (∑ i' ∈ stageSet st k', ‖Φ k' i'‖ ^ 2)
              ≤ plainConst Ca A B k' * (1 + (r - a)) ^ k' * κ a r * X *
                  (B * (Ca * κ r t * Y)) :=
                mul_le_mul_of_nonneg_left hb1
                  (mul_nonneg (mul_nonneg (mul_nonneg (plainConst_nonneg hCa hA hB k')
                    (pow_nonneg (by linarith [hr.1]) _)) (hκ a r)) hXp)
            _ ≤ A * B * Ca * plainConst Ca A B k' * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y :=
                plain_term_le hk'k (plainConst_nonneg hCa hA hB k') hB hCa hXp hY0 (hκ a r)
                  (hκ r t) (hmul r t hrI.1 hrI.2 ht.2) (by linarith [hr.1]) (by linarith [hr.2])
      _ = A * B * Ca * Sk * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y := by
          rw [hSk]
          simp only [Finset.mul_sum, Finset.sum_mul]
  have hIint : ‖∫ r in a..t, ∑ i ∈ stageSet st k,
      cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r)‖ ≤
      (t - a) * (A * B * Ca * Sk * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hat hpt intervalIntegrable_const).trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [hsum, plainConst_eq]
  exact (norm_add_le _ _).trans (plain_step_le (k := k) (fun hk0 => by subst hk0; simp)
    (by linarith) hCa (hκ a t) hXp hY0 hSk0 hinit hIint (by positivity))

end Pass

end AVRegularity.CycleWords.Seam
end
