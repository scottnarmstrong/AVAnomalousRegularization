-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.B1PlainFrame
public import AVRegularity.CycleWords.Seam.NegTest
import AVRegularity.CycleWords.Seam.OldAdjointIdentification
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.Discard.JetFourier

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Positive-weight finiteness of the reversed adjoint chain: a datum with finite weighted factorial
norm at moment `n` gives a reversed adjoint chain with finite weighted factorial norms at moment
`n` at all times (crude chart weights of the reversed drift and the finite-energy lemma for scalar
chains). -/

theorem reversedAdjoint_weighted_finite (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (ϖ : ℝ) (hϖ : 0 ≤ ϖ) (m n : ℕ) {a t : ℝ} (hat : a ≤ t) (φ : PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a)
      (fun τ z => -(v (-τ) z)) (fun _ => φ) (fun _ _ _ => 0) ψ ψw)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / (3 * Interior.negAdjointJetConstant Cvj m *
      (1 + (Real.sqrt η)⁻¹)))
    (hφ : weightedFactorialNormSq n ϖ 0 r m φ ≠ ⊤) :
    ∀ τ ∈ Icc (-t) (-a), weightedFactorialNormSq n ϖ 0 r m (ψ 0 () τ) ≠ ⊤ := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  set A := Interior.negAdjointJetConstant Cvj m with hAdef
  have hA : 1 ≤ A := Interior.one_le_negAdjointJetConstant Cvj m
  set strain := A / Real.sqrt η with hstraindef
  have hstrain0 : 0 ≤ strain := by positivity
  have hP : 1 ≤ 1 + (Real.sqrt η)⁻¹ := by
    have := inv_pos.mpr hsη
    linarith
  have hr3 : r ≤ 1 / 3 := by
    refine hr1.trans ?_
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hstrain : strain * r ^ 2 ≤ 1 / 8 := by
    set ρ := 1 / (3 * A * (1 + (Real.sqrt η)⁻¹)) with hρdef
    have hρ : 0 < ρ := by positivity
    have hsP : Real.sqrt η * (1 + (Real.sqrt η)⁻¹) = Real.sqrt η + 1 := by
      field_simp
    have hX : 1 ≤ A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹) := by
      rw [hsP]
      have h1 : 1 ≤ Real.sqrt η + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ A * (Real.sqrt η + 1) * (1 + (Real.sqrt η)⁻¹) := by gcongr
    have he : strain * ρ ^ 2 =
        1 / (9 * (A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹))) := by
      rw [hstraindef, hρdef]
      field_simp
      ring
    have hρ8 : strain * ρ ^ 2 ≤ 1 / 8 := by
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc strain * r ^ 2 ≤ strain * ρ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hr1 2) hstrain0
      _ ≤ 1 / 8 := hρ8
  set vr : ℝ → Vec 2 → Vec 2 := fun τ z => -(v (-τ) z) with hvrdef
  have hvrD : IsCellDrift vr := cellDrift_timeReverse hv
  have hvrs : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (vr τ) := fun τ => (hvs (-τ)).neg
  set V := |Cvj 0| / Real.sqrt η with hVdef
  have hV : 0 ≤ V := by positivity
  have hbv : ∀ τ z, ‖vr τ z‖ ≤ V := fun τ x => by
    have h := reversedDrift_iteratedFDeriv_le hη v hvs Cvj hvj 0 τ x
    rw [norm_iteratedFDeriv_zero] at h
    rw [hVdef, le_div_iff₀ hsη, mul_comm]
    exact h.trans (le_abs_self _)
  have hjets : ∀ l, 1 ≤ l → l ≤ m → ∀ τ x,
      ‖coefficientDerivativeArray (driftCoefficient (vr τ)) l x‖ ≤ strain * (l.factorial : ℝ) :=
    fun l _ hlm τ x => reversedDrift_jets hη v hvs Cvj hvj m τ l hlm x
  obtain ⟨W, -⟩ := crudeChartWeights_exists (fun τ => G (-τ)) (cellMetric_timeReverse hG) vr V hV
    hbv (-t) (t - a + 1) ϖ (by linarith) hϖ n
  have hsol : IsPlaneChainFrom (h := fun _ : Unit => ℝ)
      (geometryScalarData 2 (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a) vr
      (fun _ _ => φ) (fun _ _ => 0) (fun _ _ => ψ 0 ()) (fun _ _ => ψw 0 ()) := by
    unfold IsPlaneChain at hψ
    unfold IsPlaneChainFrom
    convert hψ using 2
    all_goals first
      | rfl
      | (rename_i q
         obtain ⟨j, x⟩ := q
         obtain rfl : j = 0 := Fin.fin_one_eq_zero j
         rfl)
  have hfin := constantMetric_scalar_component_energy_ne_top (E := ℝ) (-t) (-a) (by linarith) m m n
    le_rfl vr hvrD hvrs strain r hstrain0 hr (by linarith) hstrain hjets
    (fun τ => G (-τ)) (cellMetric_timeReverse hG) (-t) (t - a + 1) ϖ 0
    (fun k => 1 + crudeChartRate ϖ V k * (t - a + 1)) W le_rfl (by linarith) φ (fun _ => 0)
    (planeHk_zero_time_memLp _ _) (ψ 0 ()) (ψw 0 ()) hsol hφ (by simp)
  intro τ hτ
  refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hfin le_self_add) ?_
  exact le_iSup₂ (f := fun τ (_ : τ ∈ Icc (-t) (-a)) =>
    weightedFactorialNormSq n ϖ 0 r m (ψ 0 () τ)) τ hτ

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The bound on compact data in the two regimes

The hypothesis `hComp` of `s3b_rough_core`, for a kernel `K₊`:
* `s3b_comp_zero`: when `K₊ = 0` (a word with `Θ₊ = 0`, or a block that is not well buffered),
  by the quiet margin on the plane and the lossless low pass `μ₂`;
* `s3b_comp_good`: when `K₊ = R ∘ μ(D)` (well-buffered blocks), by the compact core. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

section Regimes

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw Kmax pout k : ℕ} {Ks : Fin Nw → ℕ} {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D}
  {S t₀ ϖ δ r : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
  {κc : Fin (Nw + 1) → ι → ℕ}

/-- **The zero kernel.** -/
theorem s3b_comp_zero (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hK0 : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → Kp g = 0) {μ₂ : Vec 2 → ℝ}
    {X₂ Ea : ℝ≥0∞} {C₅' : ℝ}
    (hCol : ∀ (f' : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hB5' : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
    (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
    (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x))
    (hcd : IsCompactDatum fk)
    (hch : IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0)
      uk wk) :
    jetOutputNorm π pout Kmax ϖ r
        (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (Kp (fun x' => planeValue (fk x')) x) z) ≤
      (X₂ * (Ea + ENNReal.ofReal C₅')) *
        negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (fk x)) := by
  have hF2 : ∀ x, MemLp (planeValue (fk x)) 2 volume :=
    fun x => planeJetOrder_memLp (Nat.zero_le _) (fk x) _
  rw [hK0 _ hF2]
  have hz : (fun x a (wd : DerivativeWord2 a) z =>
      planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
        orderedDerivative wd ((0 : ∀ x, Vec 2 → h x) x) z) =
      fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z := by
    funext x a wd z
    rw [show ((0 : ∀ x, Vec 2 → h x) x) = (fun _ => (0 : h x)) from rfl,
      orderedDerivative_zero_function, sub_zero]
  rw [hz]
  refine (hCol fk uk wk hcd hch).trans ?_
  calc X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
          (fun x => planeValue (fk x)) +
        momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (fk x))))
      ≤ X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
          (fun x => planeValue (fk x)) + ENNReal.ofReal C₅' *
            negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (fk x))) :=
        mul_le_mul_right (add_le_add le_rfl (hB5' _ hF2)) _
    _ = _ := by ring

end Regimes

/-- **The well-buffered kernel** `K₊ = R ∘ μ(D)`, through the compact core. -/
theorem s3b_comp_good {K : ScalarConstants}
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw Kmax pout k : ℕ} (hD : 2 ≤ D) {d Ks : Fin Nw → ℕ} {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    {letters : Fin Nw → CycleLetter ι h D} (hslow : ∀ i, (letters i).slow = Ks i)
    {η S ηg rstar t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {X₀ : Vec 2} {χlo μ μ₂ : Vec 2 → ℝ} (hμ : IsSeamLowPass μ)
    (hμ₂s : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hμ₂c : HasCompactSupport μ₂) (hμ₂e : ∀ θ, μ₂ (-θ) = μ₂ θ)
    (hμ₂R : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ₂ ξ = 0)
    (hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ)
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R) (hr : 0 < 2 * K.ξlo * Real.sqrt η)
    (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hKp : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      Kp g = R (fun x => fourierCutoff μ (g x)))
    {κ : Fin (Nw + 1) → ι → ℕ} (hκf : ∀ x, Kmax ≤ κ (Fin.last Nw) x) (hκ : IsWordSlots letters κ)
    (hWc : IsWordSlots letters (cappedWordSlots κ Kmax d))
    {X₁ X₂ Ea : ℝ≥0∞} (hX₁ : X₁ ≠ ⊤) (hX₂ : X₂ ≠ ⊤) (hEa : Ea ≠ ⊤) {C₁ C₅ C₅' : ℝ}
    (hEx : ∀ fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x), IsCompactDatum fk →
      ∃ (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ Kmax d j x) (h x))
        (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ Kmax d j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kmax d) t₀ (t₀ + S)
          v fk (fun _ _ _ => 0) uk wk)
    (hDis : ∀ (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kmax d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (R (fun x' => planeValue (fk x')) x) z) ≤
        X₁ * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    (hCol : ∀ (f' : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kmax d 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kmax d j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kmax d) t₀ (t₀ + S) v
        f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hB5 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ (Gf x)) ≤
        ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hB5' : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hP1 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (Gf x) volume) →
      negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ Gf)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hcd : IsCompactDatum f)
    (hch : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
      (fun _ _ _ => 0) u w) :
    jetOutputNorm π pout Kmax ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (Kp (fun x' => planeValue (f x')) x) z) ≤
      (X₁ * ENNReal.ofReal C₅ + X₂ * (Ea * (1 + ENNReal.ofReal C₁ * ENNReal.ofReal C₅))) *
        negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (f x)) := by
  rw [hKp (fun x' => planeValue (f x')) fun x => planeJetOrder_memLp (Nat.zero_le _) (f x) _]
  refine (s3b_compact_core hD hπ hslow hμ hμ₂s hμ₂c hμ₂e hμ₂R hprod hR hr hκf hκ hWc hcd hch
    hX₁ hX₂ hEa hEx hDis hCol hB5 hB5' hP1).trans (le_of_eq ?_)
  ring

/-- **The well-buffered kernel along converging data**: the jets of `R(μ φ_j)` converge to those of
`R(μ F)` when `φ_j → F` in the moment norm of weight `p_in` (lossless low pass and negative norm by moment norm for `μ(F − φ_j)`). -/
theorem s3b_klim_good {K : ScalarConstants}
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw pout k pin : ℕ} {Ks : Fin Nw → ℕ} {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    {letters : Fin Nw → CycleLetter ι h D} (hslow : ∀ i, (letters i).slow = Ks i)
    {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {X₀ : Vec 2} {χlo μ : Vec 2 → ℝ} (hμ : IsSeamLowPass μ)
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R) (hr : 0 < 2 * K.ξlo * Real.sqrt η)
    (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hKp : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      Kp g = R (fun x => fourierCutoff μ (g x)))
    (hnp : wordReserveN pout Ks ≤ pin) {C₁ C₅ : ℝ}
    (hB5 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ (Gf x)) ≤
        ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hP1 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (Gf x) volume) →
      negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ Gf)
    (F : ∀ x, Vec 2 → h x) (φs : ℕ → ∀ x, Vec 2 → h x) (hF : ∀ x, MemLp (F x) 2 volume)
    (hφ : ∀ j x, MemLp (φs j x) 2 volume)
    (hlim : Tendsto (fun j => momentNorm π pin ϖ (fun x z => F x z - φs j x z)) atTop (𝓝 0))
    (x : ι) (a : ℕ) (wd : DerivativeWord2 a) (z : Vec 2) :
    Tendsto (fun j => orderedDerivative wd (Kp (φs j) x) z) atTop
      (𝓝 (orderedDerivative wd (Kp F x) z)) := by
  have hKj : ∀ j, Kp (φs j) = R (fun x => fourierCutoff μ (φs j x)) := fun j => hKp _ (hφ j)
  simp only [hKj, hKp F hF]
  have hμF : ∀ x, MemLp (fourierCutoff μ (F x)) 2 volume := fun x =>
    fourierCutoff_memLp_of_memLp μ (Real.pi / 2) hμ.supp hμ.smooth (hF x)
  have hμφ : ∀ j x, MemLp (fourierCutoff μ (φs j x)) 2 volume := fun j x =>
    fourierCutoff_memLp_of_memLp μ (Real.pi / 2) hμ.supp hμ.smooth (hφ j x)
  have hslowF : (fun i => (letters i).slow) = Ks := funext hslow
  have hbound : ∀ j, momentNorm π (wordReserveN 0 fun i => (letters i).slow) ϖ
      (fun x z => fourierCutoff μ (F x) z - fourierCutoff μ (φs j x) z) ≤
      ENNReal.ofReal C₅ * (ENNReal.ofReal C₁ *
        momentNorm π pin ϖ (fun x z => F x z - φs j x z)) := by
    intro j
    have hsub : (fun x z => fourierCutoff μ (F x) z - fourierCutoff μ (φs j x) z) =
        fun x => fourierCutoff μ (fun z => F x z - φs j x z) := by
      funext x
      rw [s3b_fourierCutoff_sub μ (Real.pi / 2) hμ.supp hμ.smooth (hF x) (hφ j x)]
    rw [hsub, hslowF]
    refine (momentNorm_mono (n' := wordReserveN pout Ks) (by unfold wordReserveN; omega)
      _ _ _).trans ?_
    refine (hB5 _ fun x => (hF x).sub (hφ j x)).trans (mul_le_mul_right ?_ _)
    refine (hP1 _ fun x => (hF x).aestronglyMeasurable.sub (hφ j x).aestronglyMeasurable).trans
      (mul_le_mul_right (momentNorm_mono hnp _ _ _) _)
  have h0 : Tendsto (fun j => ENNReal.ofReal C₅ * (ENNReal.ofReal C₁ *
      momentNorm π pin ϖ (fun x z => F x z - φs j x z))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => ENNReal.ofReal C₅ * (ENNReal.ofReal C₁ *
        momentNorm π pin ϖ (fun x z => F x z - φs j x z))) atTop
        (𝓝 (ENNReal.ofReal C₅ * (ENNReal.ofReal C₁ * 0))) :=
      ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hlim
        (Or.inr ENNReal.ofReal_ne_top)) (Or.inr ENNReal.ofReal_ne_top)
    simpa using h1
  have hlim0 := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun j => zero_le) hbound
  exact retainedMap_orderedDerivative_tendsto amplitudePlancherel hR hr hπ
    (fun x => fourierCutoff μ (F x)) (fun j x => fourierCutoff μ (φs j x))
    (fun x => (hμF x).aestronglyMeasurable) (fun j x => (hμφ j x).aestronglyMeasurable) hlim0
    x a wd z

end AVRegularity.CycleWords.Seam
end
end

section
/-! # the low band of a moment is bounded by the moment of `μ₂(D) g`
For `g ∈ L¹ ∩ L²` with compact support and `μ₂ = 1` on `|ξ| ≤ π/4`: the transform of `y^β g` and
of `y^β μ₂(D)g` agree on `|ξ| < π/4` (the difference has transform vanishing on the ball; the
derivative of the transform is the transform of the moment), so
`∫_{|ξ|<π/8} |FT(y^β g)|² ≤ (2π)² ‖y^β μ₂(D) g‖₂²`.
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard AVRegularity.CycleWords.Seam
  Filter Topology
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal SchwartzMap

namespace AVRegularity.CycleWords.Seam.NegLowBand

open AVRegularity.CycleWords.Seam.YoungKernel

theorem continuous_momentWeight (γ : ℕ × ℕ) : Continuous fun y : Vec 2 => momentWeight γ y := by
  unfold momentWeight; fun_prop

theorem moment_integrable_compact {g : Vec 2 → ℝ} (hg : Integrable g) (hgc : HasCompactSupport g)
    (γ : ℕ × ℕ) : Integrable (fun y => momentWeight γ y * g y) volume := by
  obtain ⟨R0, hR0, hR⟩ := exists_support_radius hgc
  refine (hg.norm.const_mul (R0 ^ (γ.1 + γ.2))).mono'
    ((continuous_momentWeight γ).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : R0 < ‖y‖
  · rw [hR y hy]; simp
  · rw [not_lt] at hy
    rw [norm_mul]
    have h0 : |y 0| ≤ R0 := (coord_le_norm 0 y).trans hy
    have h1 : |y 1| ≤ R0 := (coord_le_norm 1 y).trans hy
    have : ‖momentWeight γ y‖ ≤ R0 ^ (γ.1 + γ.2) := by
      unfold momentWeight
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 _) (pow_le_pow_left₀ (abs_nonneg _) h1 _)
        (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem abs_momentWeight_le (γ : ℕ × ℕ) (y : Vec 2) :
    |momentWeight γ y| ≤ (1 + ‖y‖) ^ (γ.1 + γ.2) := by
  unfold momentWeight
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  have h0 : |y 0| ≤ 1 + ‖y‖ := by linarith [coord_le_norm 0 y]
  have h1 : |y 1| ≤ 1 + ‖y‖ := by linarith [coord_le_norm 1 y]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 _) (pow_le_pow_left₀ (abs_nonneg _) h1 _)
    (by positivity) (by positivity)

/-- The weighted `L¹` bound of a Schwartz convolution of a compactly supported integrable
function. -/
theorem schwartz_conv_weighted_integrable (K : 𝓢(Vec 2, ℝ)) {g : Vec 2 → ℝ} (hg : Integrable g)
    (hgc : HasCompactSupport g) (d : ℕ) :
    Integrable (fun x => (1 + ‖x‖) ^ d * |schwartzConvolution K g x|) volume := by
  set gd : Vec 2 → ℝ := fun y => (1 + ‖y‖) ^ d * |g y| with hgd_def
  set kd : Vec 2 → ℝ := fun u => (1 + ‖u‖) ^ d * |K u| with hkd_def
  obtain ⟨R0, hR0, hR⟩ := exists_support_radius hgc
  have hgd : Integrable gd volume := by
    refine (hg.norm.const_mul ((1 + R0) ^ d)).mono' (by
      have : Continuous fun y : Vec 2 => (1 + ‖y‖) ^ d := (continuous_const.add continuous_norm).pow d
      exact this.aestronglyMeasurable.mul hg.aestronglyMeasurable.norm)
      (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : R0 < ‖y‖
    · simp [hgd_def, hR y hy]
    · rw [not_lt] at hy
      simp only [hgd_def, Real.norm_eq_abs, abs_mul, abs_pow, abs_abs]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) d) (abs_nonneg _)
  have hkd : Integrable kd volume := by
    have := schwartz_weighted_integrable K 0 d
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp [hkd_def, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have hH : Integrable (fun x => ∫ y, gd y * kd (x - y)) volume := by
    have := Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hgd hkd
    exact this
  have hUc : Continuous (schwartzConvolution K g) :=
    (schwartzConvolution_contDiff K g hg).continuous
  refine hH.mono' (((continuous_const.add continuous_norm).pow d).mul hUc.abs).aestronglyMeasurable ?_
  filter_upwards [hgd.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hkd] with x hx
  have hx' : Integrable (fun y => gd y * kd (x - y)) volume := by
    simpa [ConvolutionExistsAt] using hx
  rw [Real.norm_of_nonneg (by positivity)]
  unfold schwartzConvolution
  have h1 : |∫ y, K (x - y) • g y| ≤ ∫ y, |K (x - y)| * |g y| := by
    have := norm_integral_le_integral_norm (μ := volume) (fun y => K (x - y) • g y)
    simpa [norm_smul, Real.norm_eq_abs] using this
  have hi : Integrable (fun y => |K (x - y)| * |g y|) volume := by
    have := (schwartzConvolution_integrable K g hg x).norm
    simpa [norm_smul, Real.norm_eq_abs] using this
  calc (1 + ‖x‖) ^ d * |∫ y, K (x - y) • g y|
      ≤ (1 + ‖x‖) ^ d * ∫ y, |K (x - y)| * |g y| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ∫ y, (1 + ‖x‖) ^ d * (|K (x - y)| * |g y|) := (integral_const_mul _ _).symm
    _ ≤ ∫ y, gd y * kd (x - y) := by
        refine integral_mono (hi.const_mul _) hx' fun y => ?_
        have hn : 1 + ‖x‖ ≤ (1 + ‖y‖) * (1 + ‖x - y‖) := by
          have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
            calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
              _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
          nlinarith [norm_nonneg y, norm_nonneg (x - y)]
        have hp : (1 + ‖x‖) ^ d ≤ (1 + ‖y‖) ^ d * (1 + ‖x - y‖) ^ d := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hn d
        simp only [hgd_def, hkd_def]
        calc (1 + ‖x‖) ^ d * (|K (x - y)| * |g y|)
            ≤ ((1 + ‖y‖) ^ d * (1 + ‖x - y‖) ^ d) * (|K (x - y)| * |g y|) :=
              mul_le_mul_of_nonneg_right hp (by positivity)
          _ = _ := by ring

theorem moment_cutoff_integrable (μ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ)
    (hc : HasCompactSupport μ) {g : Vec 2 → ℝ} (hg : Integrable g) (hgc : HasCompactSupport g)
    (γ : ℕ × ℕ) : Integrable (fun y => momentWeight γ y * fourierCutoff μ g y) volume := by
  obtain ⟨R, hR⟩ := radius' μ hc
  have h := schwartz_conv_weighted_integrable (seamRealCutoffSchwartz μ R hR hs) hg hgc
    (γ.1 + γ.2)
  have hU : fourierCutoff μ g = schwartzConvolution (seamRealCutoffSchwartz μ R hR hs) g :=
    fourierCutoff_eq_conv μ R hR hs g
  rw [← hU] at h
  have hUc : Continuous (fourierCutoff μ g) := (fourierCutoff_contDiff μ hs hc hg).continuous
  refine h.mono' ((continuous_momentWeight γ).aestronglyMeasurable.mul hUc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (abs_momentWeight_le γ y) le_rfl (abs_nonneg _) (by positivity)

theorem ftIntegrand_integrable {g : Vec 2 → ℝ} (hg : Integrable g) (ξ : Vec 2) :
    Integrable (fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot ξ y : ℂ))) * (g y : ℂ)) volume := by
  have hc : Continuous fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot ξ y : ℂ))) := by
    have : Continuous fun y : Vec 2 => vecDot ξ y := by unfold vecDot; fun_prop
    fun_prop
  refine hg.norm.mono' (hc.aestronglyMeasurable.mul hg.ofReal.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_exp]
  simp

theorem Ft_sub {f g : Vec 2 → ℝ} (hf : Integrable f) (hg : Integrable g) (ξ : Vec 2) :
    planeTransform (fun y => f y - g y) ξ = planeTransform f ξ - planeTransform g ξ := by
  unfold planeTransform
  rw [← integral_sub (ftIntegrand_integrable hf ξ) (ftIntegrand_integrable hg ξ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

/-- One step of the induction: the derivative of a transform vanishing on an open ball. -/
theorem ft_step_zero {r : ℝ} {g : Vec 2 → ℝ} (hg : Integrable g) (j : Fin 2)
    (hgj : Integrable (fun y : Vec 2 => y j * g y))
    (hz : ∀ ξ, vecDot ξ ξ < r ^ 2 → planeTransform g ξ = 0) :
    ∀ ξ, vecDot ξ ξ < r ^ 2 → planeTransform (fun y => y j * g y) ξ = 0 := by
  intro ξ hξ
  have hd := Ft_hasDerivAt hg j hgj ξ
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), planeTransform g (ξ + t • basisVec j) = 0 := by
    have hcont : Continuous fun t : ℝ => vecDot (ξ + t • basisVec j) (ξ + t • basisVec j) := by
      unfold vecDot; fun_prop
    have : ∀ᶠ t in 𝓝 (0 : ℝ), vecDot (ξ + t • basisVec j) (ξ + t • basisVec j) < r ^ 2 := by
      refine hcont.continuousAt.eventually_lt continuousAt_const ?_
      simpa using hξ
    filter_upwards [this] with t ht using hz _ ht
  have h0 : HasDerivAt (fun t : ℝ => planeTransform g (ξ + t • basisVec j)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq (by
      filter_upwards [hev] with t ht using ht)
  have := hd.unique h0
  have hI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
  exact (mul_eq_zero.1 this).resolve_left hI

/-- **Lemma Z.** If all moments are integrable and the transform vanishes on an open ball, so do
the transforms of all moments. -/
theorem ft_moment_zero {r : ℝ} {f : Vec 2 → ℝ} (hint : ∀ γ : ℕ × ℕ,
      Integrable (fun y => momentWeight γ y * f y) volume)
    (hz : ∀ ξ, vecDot ξ ξ < r ^ 2 → planeTransform f ξ = 0) (β : ℕ × ℕ) :
    ∀ ξ, vecDot ξ ξ < r ^ 2 → planeTransform (fun y => momentWeight β y * f y) ξ = 0 := by
  have h00 : ∀ ξ, vecDot ξ ξ < r ^ 2 → planeTransform (fun y => momentWeight (0, 0) y * f y) ξ = 0 := by
    intro ξ hξ
    have : (fun y => momentWeight (0, 0) y * f y) = f := by
      funext y; simp [momentWeight]
    rw [this]; exact hz ξ hξ
  have hfirst : ∀ k : ℕ, ∀ ξ, vecDot ξ ξ < r ^ 2 →
      planeTransform (fun y => momentWeight (k, 0) y * f y) ξ = 0 := by
    intro k
    induction k with
    | zero => exact h00
    | succ k ih =>
      have := ft_step_zero (hint (k, 0)) 0 (by
        have h := hint (k + 1, 0)
        refine h.congr (Filter.Eventually.of_forall fun y => ?_)
        simp only [momentWeight]; ring) ih
      intro ξ hξ
      have e : (fun y => momentWeight (k + 1, 0) y * f y) =
          fun y => y 0 * (momentWeight (k, 0) y * f y) := by
        funext y; simp only [momentWeight]; ring
      rw [e]; exact this ξ hξ
  have hsecond : ∀ l : ℕ, ∀ ξ, vecDot ξ ξ < r ^ 2 →
      planeTransform (fun y => momentWeight (β.1, l) y * f y) ξ = 0 := by
    intro l
    induction l with
    | zero => exact hfirst β.1
    | succ l ih =>
      have := ft_step_zero (hint (β.1, l)) 1 (by
        have h := hint (β.1, l + 1)
        refine h.congr (Filter.Eventually.of_forall fun y => ?_)
        simp only [momentWeight]; ring) ih
      intro ξ hξ
      have e : (fun y => momentWeight (β.1, l + 1) y * f y) =
          fun y => y 1 * (momentWeight (β.1, l) y * f y) := by
        funext y; simp only [momentWeight]; ring
      rw [e]; exact this ξ hξ
  exact hsecond β.2

/-- The transform of `μ(D) g` is `μ ĝ`, pointwise. -/
theorem ft_cutoff_eq (μ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (hc : HasCompactSupport μ)
    (hev : ∀ θ, μ (-θ) = μ θ) {g : Vec 2 → ℝ} (hg : Integrable g) (hg2 : MemLp g 2 volume)
    (ξ : Vec 2) : planeTransform (fourierCutoff μ g) ξ = (μ ξ : ℂ) * planeTransform g ξ := by
  obtain ⟨R, hR⟩ := radius' μ hc
  have hU1 := fourierCutoff_integrable μ R hR hs hg
  have hU2 := fourierCutoff_memLp μ R hR hs hg2
  obtain ⟨hh, hft⟩ := cutoff_base μ hs hc hev hg hg2
  have h1 := fourierL2_of_integrable hU1 hU2
  have hae : (fun x : Vec 2 => planeTransform (fourierCutoff μ g) ((2 * Real.pi) • x)) =ᵐ[volume]
      fun x => (μ ((2 * Real.pi) • x) : ℂ) * planeTransform g ((2 * Real.pi) • x) := by
    filter_upwards [h1, hft] with x hx1 hx2
    rw [← hx1]
    exact hx2
  have hcl : Continuous fun x : Vec 2 => planeTransform (fourierCutoff μ g) ((2 * Real.pi) • x) :=
    (Ft_continuous hU1).comp (continuous_const_smul _)
  have hcr : Continuous fun x : Vec 2 => (μ ((2 * Real.pi) • x) : ℂ) *
      planeTransform g ((2 * Real.pi) • x) :=
    (Complex.continuous_ofReal.comp (hs.continuous.comp (continuous_const_smul _))).mul
      ((Ft_continuous hg).comp (continuous_const_smul _))
  have := (Continuous.ae_eq_iff_eq volume hcl hcr).1 hae
  have h2 := congrFun this ((2 * Real.pi)⁻¹ • ξ)
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have e : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]
  simp only [e] at h2
  exact h2

/-- **The low band of one moment.** -/
theorem low_scalar (μ₂ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hc : HasCompactSupport μ₂)
    (hev : ∀ θ, μ₂ (-θ) = μ₂ θ) (h1 : ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ Real.pi / 4 → μ₂ ξ = 1)
    {g : Vec 2 → ℝ} (hg : Integrable g) (hgc : HasCompactSupport g) (hg2 : MemLp g 2 volume)
    (β : ℕ × ℕ) :
    ∫⁻ ξ, lowBandIntegrand (Real.pi / 8) (fun y => momentWeight β y * g y) ξ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ∫⁻ z, ENNReal.ofReal ((momentWeight β z * fourierCutoff μ₂ g z) ^ 2) := by
  set U := fourierCutoff μ₂ g with hUdef
  have hmg := moment_integrable_compact hg hgc
  have hmU := moment_cutoff_integrable μ₂ hs hc hg hgc
  have hΔ : ∀ γ : ℕ × ℕ, Integrable (fun y => momentWeight γ y * (g y - U y)) volume := by
    intro γ
    have := (hmg γ).sub (hmU γ)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]; ring
  have hU1 : Integrable U volume := by
    have := hmU (0, 0)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [momentWeight, hUdef]
  have hzero : ∀ ξ, vecDot ξ ξ < (Real.pi / 4) ^ 2 → planeTransform (fun y => g y - U y) ξ = 0 := by
    intro ξ hξ
    rw [Ft_sub hg hU1, hUdef, ft_cutoff_eq μ₂ hs hc hev hg hg2,
      h1 ξ (Real.sqrt_le_iff.2 ⟨by positivity, hξ.le⟩)]
    simp
  have hZ := ft_moment_zero hΔ hzero β
  have heq : ∀ ξ, vecDot ξ ξ < (Real.pi / 4) ^ 2 →
      planeTransform (fun y => momentWeight β y * g y) ξ = planeTransform (fun y => momentWeight β y * U y) ξ := by
    intro ξ hξ
    have := Ft_sub (hmg β) (hmU β) ξ
    have h0 := hZ ξ hξ
    have e : (fun y => momentWeight β y * (g y - U y)) =
        fun y => momentWeight β y * g y - momentWeight β y * U y := by
      funext y; ring
    rw [e, this] at h0
    exact sub_eq_zero.1 h0
  -- pointwise comparison of the integrands
  have hpt : ∀ ξ, lowBandIntegrand (Real.pi / 8) (fun y => momentWeight β y * g y) ξ ≤
      ENNReal.ofReal (‖planeTransform (fun y => momentWeight β y * U y) ξ‖ ^ 2) := by
    intro ξ
    unfold lowBandIntegrand
    split_ifs with hξ
    · have hlt : vecDot ξ ξ < (Real.pi / 4) ^ 2 := by
        refine hξ.trans_le ?_
        have := Real.pi_pos
        nlinarith
      rw [heq ξ hlt]
    · exact zero_le
  by_cases htop : ∫⁻ z, ENNReal.ofReal ((momentWeight β z * U z) ^ 2) = ⊤
  · rw [htop, ENNReal.mul_top (by simp)]
    exact le_top
  have hUc : Continuous U := (fourierCutoff_contDiff μ₂ hs hc hg).continuous
  have hmem : MemLp (fun z => momentWeight β z * U z) 2 volume :=
    memLp_of_lintegral_sq_ne_top ((continuous_momentWeight β).aestronglyMeasurable.mul
      hUc.aestronglyMeasurable) htop
  have hft := fourierL2_of_integrable (hmU β) hmem
  have hpl := plancherel_of_hasFT (v := fun z => momentWeight β z * U z)
    (Φ := planeTransform (fun y => momentWeight β y * U y)) ⟨hmem, hft⟩
    (Ft_continuous (hmU β)).measurable
  calc ∫⁻ ξ, lowBandIntegrand (Real.pi / 8) (fun y => momentWeight β y * g y) ξ
      ≤ ∫⁻ ξ, ENNReal.ofReal (‖planeTransform (fun y => momentWeight β y * U y) ξ‖ ^ 2) :=
        lintegral_mono hpt
    _ = ∫⁻ ξ, ‖planeTransform (fun y => momentWeight β y * U y) ξ‖ₑ ^ 2 := by
        refine lintegral_congr fun ξ => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∫⁻ z, ENNReal.ofReal ((momentWeight β z * U z) ^ 2) := by
        rw [hpl, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
          ENNReal.ofReal_one, one_mul]

end AVRegularity.CycleWords.Seam.NegLowBand
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The kernel in its two regimes, at a block

The hypotheses of `s3b_rough_core` on the kernel `K₊` (smooth outputs, congruence, convergence
along converging data) and on compact data (`hComp`), in the two regimes:
* `s3b_regime_good`: `K₊ = R ∘ μ(D)` with a retained map `R` (well-buffered blocks, `Θ₊ ≠ 0`);
* `s3b_regime_zero`: `K₊ = 0` on square-integrable fields. -/

section
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- **The well-buffered regime.** -/
theorem s3b_regime_good {K : ScalarConstants}
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw Kmax pout k pin : ℕ} (hD : 2 ≤ D) {d Ks : Fin Nw → ℕ} {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    {letters : Fin Nw → CycleLetter ι h D} (hslow : ∀ i, (letters i).slow = Ks i)
    {η S ηg rstar t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {X₀ : Vec 2} {χlo μ μ₂ : Vec 2 → ℝ} (hμ : IsSeamLowPass μ)
    (hμ₂s : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hμ₂c : HasCompactSupport μ₂) (hμ₂e : ∀ θ, μ₂ (-θ) = μ₂ θ)
    (hμ₂R : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ₂ ξ = 0)
    (hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ)
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R) (hr : 0 < 2 * K.ξlo * Real.sqrt η)
    (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hKp : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      Kp g = R (fun x => fourierCutoff μ (g x)))
    (hnp : wordReserveN pout Ks ≤ pin)
    {κc : Fin (Nw + 1) → ι → ℕ} (hκcl : ∀ x, Kmax ≤ κc (Fin.last Nw) x)
    (hκc : IsWordSlots letters κc) (hWcc : IsWordSlots letters (cappedWordSlots κc Kmax d))
    {X₁ X₂ Ea : ℝ≥0∞} (hX₁ : X₁ ≠ ⊤) (hX₂ : X₂ ≠ ⊤) (hEa : Ea ≠ ⊤) {C₁ C₅ C₅' : ℝ}
    (hEx : ∀ fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κc Kmax d 0 x) (h x), IsCompactDatum fk →
      ∃ (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κc Kmax d j x) (h x))
        (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κc Kmax d j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κc Kmax d) t₀ (t₀ + S)
          v fk (fun _ _ _ => 0) uk wk)
    (hDis : ∀ (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κc Kmax d 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κc Kmax d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (R (fun x' => planeValue (fk x')) x) z) ≤
        X₁ * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    (hCol : ∀ (f' : ∀ x, PlaneHk Set.univ (cappedWordSlots κc Kmax d 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κc Kmax d) t₀ (t₀ + S) v
        f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hB5 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ (Gf x)) ≤
        ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hB5' : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hP1 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (Gf x) volume) →
      negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ Gf) :
    (∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → ∀ x (M : ℕ),
      ContDiff ℝ M (Kp g x)) ∧
    (∀ g g' : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → (∀ x, MemLp (g' x) 2 volume) →
      (∀ x, g x =ᵐ[volume] g' x) → Kp g = Kp g') ∧
    (∀ (F : ∀ x, Vec 2 → h x) (φs : ℕ → ∀ x, Vec 2 → h x),
      (∀ x, MemLp (F x) 2 volume) → (∀ j x, MemLp (φs j x) 2 volume) →
      Tendsto (fun j => momentNorm π pin ϖ (fun x z => F x z - φs j x z)) atTop (𝓝 0) →
      ∀ x a (wd : DerivativeWord2 a) z, Tendsto (fun j => orderedDerivative wd (Kp (φs j) x) z)
        atTop (𝓝 (orderedDerivative wd (Kp F x) z))) ∧
    (∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0)
        uk wk →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (Kp (fun x' => planeValue (fk x')) x) z) ≤
        (X₁ * ENNReal.ofReal C₅ + X₂ * (Ea * (1 + ENNReal.ofReal C₁ * ENNReal.ofReal C₅))) *
          negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (fk x))) := by
  refine ⟨fun g hg x M => ?_, fun g g' hg hg' he => ?_, fun F φs hF hφ hlim x a wd z => ?_,
    fun fk uk wk hcd hch => ?_⟩
  · rw [hKp g hg]
    exact (hR.band _ x).1 M
  · rw [hKp g hg, hKp g' hg']
    congr 1
    funext x
    exact fourierCutoff_congr_ae' μ (he x)
  · exact s3b_klim_good hπ hslow hμ hR hr Kp hKp hnp hB5 hP1 F φs hF hφ hlim x a wd z
  · exact s3b_comp_good hD hπ hslow hμ hμ₂s hμ₂c hμ₂e hμ₂R hprod hR hr Kp hKp hκcl hκc hWcc hX₁
      hX₂ hEa hEx hDis hCol hB5 hB5' hP1 fk uk wk hcd hch

/-- **The zero kernel.** -/
theorem s3b_regime_zero
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw Kmax pout k pin : ℕ} {Ks : Fin Nw → ℕ} {π : ι → ℝ}
    {letters : Fin Nw → CycleLetter ι h D}
    {S t₀ ϖ δ r : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {X₀ : Vec 2} {μ₂ : Vec 2 → ℝ}
    (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hK0 : ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → Kp g = 0)
    {κc : Fin (Nw + 1) → ι → ℕ} {X₂ Ea : ℝ≥0∞} {C₅' : ℝ}
    (hCol : ∀ (f' : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hB5' : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf) :
    (∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → ∀ x (M : ℕ),
      ContDiff ℝ M (Kp g x)) ∧
    (∀ g g' : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → (∀ x, MemLp (g' x) 2 volume) →
      (∀ x, g x =ᵐ[volume] g' x) → Kp g = Kp g') ∧
    (∀ (F : ∀ x, Vec 2 → h x) (φs : ℕ → ∀ x, Vec 2 → h x),
      (∀ x, MemLp (F x) 2 volume) → (∀ j x, MemLp (φs j x) 2 volume) →
      Tendsto (fun j => momentNorm π pin ϖ (fun x z => F x z - φs j x z)) atTop (𝓝 0) →
      ∀ x a (wd : DerivativeWord2 a) z, Tendsto (fun j => orderedDerivative wd (Kp (φs j) x) z)
        atTop (𝓝 (orderedDerivative wd (Kp F x) z))) ∧
    (∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ r
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (Kp (fun x' => planeValue (fk x')) x) z) ≤
        (X₂ * (Ea + ENNReal.ofReal C₅')) *
          negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (fk x))) := by
  refine ⟨fun g hg x M => ?_, fun g g' hg hg' _ => ?_, fun F φs hF hφ _ x a wd z => ?_,
    fun fk uk wk hcd hch => s3b_comp_zero Kp hK0 hCol hB5' fk uk wk hcd hch⟩
  · rw [hK0 g hg]
    exact contDiff_zero_fun
  · rw [hK0 g hg, hK0 g' hg']
  · simp only [hK0 F hF, hK0 (φs _) (hφ _)]
    exact tendsto_const_nhds

/-- **The kernel in its regime**: the hypotheses of `s3b_rough_core` on the kernel and on compact
data, with the bound `B_c` of the regime. -/
theorem s3b_regime_exists {K : ScalarConstants}
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw Kmax pout k pin : ℕ} (hD : 2 ≤ D) {d Ks : Fin Nw → ℕ} {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    {letters : Fin Nw → CycleLetter ι h D} (hslow : ∀ i, (letters i).slow = Ks i)
    {η S ηg rstar t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {X₀ : Vec 2} {χlo μ μ₂ : Vec 2 → ℝ} (hμ : IsSeamLowPass μ)
    (hμ₂s : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hμ₂c : HasCompactSupport μ₂) (hμ₂e : ∀ θ, μ₂ (-θ) = μ₂ θ)
    (hμ₂R : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ₂ ξ = 0)
    (hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ) (hr : 0 < 2 * K.ξlo * Real.sqrt η)
    (Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)) (good : Prop)
    (hgood : good → ∃ R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
      IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R ∧
      ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
        Kp g = R (fun x => fourierCutoff μ (g x)))
    (hzero : ¬good → ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → Kp g = 0)
    (hnp : wordReserveN pout Ks ≤ pin)
    {κc : Fin (Nw + 1) → ι → ℕ} (hκcl : ∀ x, Kmax ≤ κc (Fin.last Nw) x)
    (hκc : IsWordSlots letters κc) (hWcc : IsWordSlots letters (cappedWordSlots κc Kmax d))
    {X₁ X₂ Ea β : ℝ≥0∞} (hX₁ : X₁ ≠ ⊤) (hX₂ : X₂ ≠ ⊤) (hEa : Ea ≠ ⊤) {C₁ C₅ C₅' : ℝ}
    (hEx : ∀ fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κc Kmax d 0 x) (h x), IsCompactDatum fk →
      ∃ (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κc Kmax d j x) (h x))
        (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κc Kmax d j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κc Kmax d) t₀ (t₀ + S)
          v fk (fun _ _ _ => 0) uk wk)
    (hDsAt : ∀ R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
      IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R →
      ∀ (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κc Kmax d 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κc Kmax d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
            orderedDerivative wd (R (fun x' => planeValue (fk x')) x) z) ≤
        X₁ * momentNorm π (wordReserveN pout Ks) ϖ (fun x => planeValue (fk x)))
    (hColc : ∀ (f' : ∀ x, PlaneHk Set.univ (cappedWordSlots κc Kmax d 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κc Kmax d j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κc Kmax d) t₀ (t₀ + S) v
        f' (fun _ _ _ => 0) u' w' →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hColk : ∀ (f' : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
      IsCompactDatum f' →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κc t₀ (t₀ + S) v f' (fun _ _ _ => 0)
        u' w' →
      jetOutputNorm π pout Kmax ϖ rstar
          (fun x a wd z => planeJetOrder (u' (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        X₂ * (Ea * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1
            (fun x => planeValue (f' x)) +
          momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (planeValue (f' x)))))
    (hB5 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ (Gf x)) ≤
        ENNReal.ofReal C₅ * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hB5' : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, MemLp (Gf x) 2 volume) →
      momentNorm π (wordReserveN pout Ks) ϖ (fun x => fourierCutoff μ₂ (Gf x)) ≤
        ENNReal.ofReal C₅' * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf)
    (hP1 : ∀ Gf : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (Gf x) volume) →
      negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 Gf ≤
        ENNReal.ofReal C₁ * momentNorm π (wordReserveN pout Ks) ϖ Gf)
    (hsg : X₁ * ENNReal.ofReal C₅ + X₂ * (Ea * (1 + ENNReal.ofReal C₁ * ENNReal.ofReal C₅)) ≤ β)
    (hsz : ¬good → X₂ * (Ea + ENNReal.ofReal C₅') ≤ β) :
    ∃ Bc : ℝ≥0∞, Bc ≠ ⊤ ∧
      (∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → ∀ x (M : ℕ),
        ContDiff ℝ M (Kp g x)) ∧
      (∀ g g' : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) → (∀ x, MemLp (g' x) 2 volume) →
        (∀ x, g x =ᵐ[volume] g' x) → Kp g = Kp g') ∧
      (∀ (F : ∀ x, Vec 2 → h x) (φs : ℕ → ∀ x, Vec 2 → h x),
        (∀ x, MemLp (F x) 2 volume) → (∀ j x, MemLp (φs j x) 2 volume) →
        Tendsto (fun j => momentNorm π pin ϖ (fun x z => F x z - φs j x z)) atTop (𝓝 0) →
        ∀ x a (wd : DerivativeWord2 a) z, Tendsto (fun j => orderedDerivative wd (Kp (φs j) x) z)
          atTop (𝓝 (orderedDerivative wd (Kp F x) z))) ∧
      (∀ (fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x))
        (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x))
        (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)),
        IsCompactDatum fk →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0)
          uk wk →
        jetOutputNorm π pout Kmax ϖ rstar
            (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z -
              orderedDerivative wd (Kp (fun x' => planeValue (fk x')) x) z) ≤
          Bc * negJetNorm π ((wordReserveN pout Ks : ℕ) : ℝ) k ϖ 1 (fun x => planeValue (fk x))) ∧
      Bc ≤ β := by
  by_cases hg : good
  · obtain ⟨R, hR, hKp⟩ := hgood hg
    obtain ⟨hKs, hKc, hKlim, hComp⟩ := s3b_regime_good hD hπ hslow hμ hμ₂s hμ₂c hμ₂e hμ₂R hprod
      hR hr Kp hKp hnp hκcl hκc hWcc hX₁ hX₂ hEa hEx (hDsAt R hR) hColc hB5 hB5' hP1
    exact ⟨_, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hX₁ ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top hX₂ (ENNReal.mul_ne_top hEa (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩))⟩,
      hKs, hKc, hKlim, hComp, hsg⟩
  · obtain ⟨hKs, hKc, hKlim, hComp⟩ := s3b_regime_zero (pin := pin) Kp (hzero hg) hColk hB5'
    exact ⟨_, ENNReal.mul_ne_top hX₂ (ENNReal.add_ne_top.2 ⟨hEa, ENNReal.ofReal_ne_top⟩),
      hKs, hKc, hKlim, hComp, hsz hg⟩
end

/-! # Tools for the fast remainder on rough data

`s3b_ae_subseq` (an almost everywhere convergent subsequence of the jets of a sequence converging
in `PlaneHk`) and `s3b_pair_le` (weak continuity on the difference of the rough chain and a compact
chain, truncated to common slots). The core `s3b_rough_core` is in `S3bRoughMain.lean`.

Route (as `rff_core`). Compact `φ_j → f` in the moment norm of weight `p_in`; their
chains at slots carrying `K_max` derivatives; the endpoints `V_j` are Cauchy in `PlaneHk K_max`;
their limit `L` agrees with the rough endpoint up to the orders `K_out x` (weak continuity on the
difference of the two chains at the minimum of the slots, after truncation to `K_out x`); Fatou
along an almost everywhere convergent subsequence; the weighted output norm by the molecular one;
`‖φ_j‖_neg ≤ ‖f‖_neg + C₁‖f − φ_j‖_mom`. -/

section
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- An almost everywhere convergent subsequence of the jets, for a sequence converging in
`PlaneHk`. -/
theorem s3b_ae_subseq {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {Kf : ℕ} (V : ℕ → ∀ x, PlaneHk Set.univ Kf (h x))
    (T : ∀ x, PlaneHk Set.univ Kf (h x)) (hVT : ∀ x, Tendsto (fun k => V k x) atTop (𝓝 (T x))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ x a (wd : DerivativeWord2 a), ∀ᵐ z, Tendsto
      (fun i => planeJetOrder (V (ns i) x) a wd z) atTop (𝓝 (planeJetOrder (T x) a wd z)) := by
  classical
  let Sf : ℕ → Vec 2 → ℝ := fun k z => ∑ p : ι × JetIndex2 Kf,
    ‖planeJetOrder (V k p.1) p.2.1.val p.2.2 z - planeJetOrder (T p.1) p.2.1.val p.2.2 z‖
  have hjet : ∀ x (i : JetIndex2 Kf), Tendsto (fun k => eLpNorm (fun z =>
      ‖planeJetOrder (V k x) i.1.val i.2 z - planeJetOrder (T x) i.1.val i.2 z‖) 2 volume)
      atTop (𝓝 0) := by
    intro x i
    have hn : Tendsto (fun k => ENNReal.ofReal ‖V k x - T x‖) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal ((tendsto_iff_norm_sub_tendsto_zero).1 (hVT x))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn (fun k => zero_le)
      (fun k => ?_)
    rw [eLpNorm_norm (fun z => planeJetOrder (V k x) i.1.val i.2 z -
      planeJetOrder (T x) i.1.val i.2 z) ((planeJetOrder_aestronglyMeasurable (V k x) _ _).sub
        (planeJetOrder_aestronglyMeasurable (T x) _ _))]
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (rff_eLpNorm_jet_le_norm (Nat.lt_succ_iff.1 i.1.isLt) (V k x - T x) i.2)
    exact (planeJetOrder_sub_ae (Nat.lt_succ_iff.1 i.1.isLt) (V k x) (T x) i.2).symm
  have hS : Tendsto (fun k => eLpNorm (Sf k - 0) 2 volume) atTop (𝓝 0) := by
    have hsum : Tendsto (fun k => ∑ p : ι × JetIndex2 Kf, eLpNorm (fun z =>
        ‖planeJetOrder (V k p.1) p.2.1.val p.2.2 z - planeJetOrder (T p.1) p.2.1.val p.2.2 z‖)
        2 volume) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (ι × JetIndex2 Kf))
        fun p _ => hjet p.1 p.2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
      (fun k => ?_)
    rw [sub_zero]
    have he : Sf k = ∑ p : ι × JetIndex2 Kf, fun z =>
        ‖planeJetOrder (V k p.1) p.2.1.val p.2.2 z - planeJetOrder (T p.1) p.2.1.val p.2.2 z‖ := by
      funext z
      simp only [Sf, Finset.sum_apply]
    rw [he]
    exact eLpNorm_sum_le (by norm_num)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (f := Sf) (g := 0) (by norm_num) hS).exists_seq_tendsto_ae
  refine ⟨ns, hns, fun x a wd => ?_⟩
  by_cases ha : a ≤ Kf
  · filter_upwards [hae] with z hz
    have hz' : Tendsto (fun i => Sf (ns i) z) atTop (𝓝 0) := by simpa using hz
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hz'
    exact Finset.single_le_sum (f := fun p : ι × JetIndex2 Kf =>
      ‖planeJetOrder (V (ns i) p.1) p.2.1.val p.2.2 z -
        planeJetOrder (T p.1) p.2.1.val p.2.2 z‖)
      (fun p _ => norm_nonneg _) (Finset.mem_univ (x, ⟨⟨a, Nat.lt_succ_of_le ha⟩, wd⟩))
  · refine Filter.Eventually.of_forall fun z => ?_
    have h0 : ∀ U : PlaneHk Set.univ Kf (h x), planeJetOrder U a wd z = 0 := fun U => by
      simp [planeJetOrder, ha]
    simp only [h0]
    exact tendsto_const_nhds

/-- **The pairing step**: weak continuity on the difference of the rough chain and a
compact chain, both truncated to common slots `κ_m`. -/
theorem s3b_pair_le
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw n : ℕ} (hD : 2 ≤ D) {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D}
    {S t₀ ϖ δ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
    {κF κc κm : Fin (Nw + 1) → ι → ℕ} (hκF : IsWordSlots letters κF)
    (hκc : IsWordSlots letters κc) (hκm : IsWordSlots letters κm)
    (hmF : ∀ j x, κm j x ≤ κF j x) (hmc : ∀ j x, κm j x ≤ κc j x)
    {fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x)}
    {uF : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x)}
    {wF : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x)}
    (hch : IsPlaneChain (wordChainData G letters X₀ δ) κF t₀ (t₀ + S) v fF (fun _ _ _ => 0) uF wF)
    {fk : ∀ x, PlaneHk Set.univ (κc 0 x) (h x)}
    {uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x) (h x)}
    {wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κc j x + 1) (h x)}
    (hchk : IsPlaneChain (wordChainData G letters X₀ δ) κc t₀ (t₀ + S) v fk (fun _ _ _ => 0) uk wk)
    {φ : ∀ x, Vec 2 → h x} (hfk : ∀ x, planeValue (fk x) =ᵐ[volume] φ x)
    (hfin : momentNorm π n ϖ (fun x z => planeValue (fF x) z - φ x z) < ⊤)
    (Φ : ∀ x, Vec 2 → h x) {C : ℝ}
    (hW : ∀ (f' : ∀ x, PlaneHk Set.univ (κm 0 x) (h x))
      (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κm j x) (h x))
      (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κm j x + 1) (h x)),
      momentNorm π n ϖ (fun x => planeValue (f' x)) < ⊤ →
      IsPlaneChain (wordChainData G letters X₀ δ) κm t₀ (t₀ + S) v f' (fun _ _ _ => 0) u' w' →
      ENNReal.ofReal |∑ x, (π x)⁻¹ *
          ∫ z, inner ℝ (planeValue (u' (Fin.last Nw) x (t₀ + S)) z) (Φ x z)| ≤
        ENNReal.ofReal C * momentNorm π n ϖ (fun x => planeValue (f' x))) :
    ENNReal.ofReal |∑ x, (π x)⁻¹ * ∫ z, inner ℝ (planeValue (uF (Fin.last Nw) x (t₀ + S)) z -
        planeValue (uk (Fin.last Nw) x (t₀ + S)) z) (Φ x z)| ≤
      ENNReal.ofReal C * momentNorm π n ϖ (fun x z => planeValue (fF x) z - φ x z) := by
  have hchF := isPlaneChain_truncate hD G letters X₀ δ t₀ (t₀ + S) v κF κm hmF hκF hκm fF uF wF hch
  have hchc := isPlaneChain_truncate hD G letters X₀ δ t₀ (t₀ + S) v κc κm hmc hκc hκm fk uk wk hchk
  have hdiff := isPlaneChain_trunc_sub hD G letters X₀ δ t₀ (t₀ + S) v κm κm
    (fun _ _ => le_rfl) hκm hκm _ _ _ _ _ _ hchF hchc
  have hval : ∀ x, planeValue ((1 : ℝ) • truncatePlaneHk (le_refl _)
      (truncatePlaneHk (hmF 0 x) (fF x)) + (-1 : ℝ) • truncatePlaneHk (hmc 0 x) (fk x))
      =ᵐ[volume] fun z => planeValue (fF x) z - φ x z := by
    intro x
    filter_upwards [planeJetOrder_trunc_sub_ae (le_refl _) (truncatePlaneHk (hmF 0 x) (fF x))
      (truncatePlaneHk (hmc 0 x) (fk x)) (Nat.zero_le _) (fun i => i.elim0), hfk x] with z h1 h2
    rw [planeValue, h1]
    change planeValue (truncatePlaneHk (hmF 0 x) (fF x)) z -
      planeValue (truncatePlaneHk (hmc 0 x) (fk x)) z = _
    rw [planeValue_truncate, planeValue_truncate, h2]
  have hm := momentNorm_congr_ae' π n ϖ hval
  have hb := hW _ _ _ (by rw [hm]; exact hfin) hdiff
  rw [hm] at hb
  refine le_trans (le_of_eq ?_) hb
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [planeJetOrder_trunc_sub_ae (le_refl _)
    (truncatePlaneHk (hmF (Fin.last Nw) x) (uF (Fin.last Nw) x (t₀ + S)))
    (truncatePlaneHk (hmc (Fin.last Nw) x) (uk (Fin.last Nw) x (t₀ + S))) (Nat.zero_le _)
    (fun i => i.elim0)] with z hz
  change _ = inner ℝ (planeJetOrder ((1 : ℝ) • truncatePlaneHk (le_refl _)
    (truncatePlaneHk (hmF (Fin.last Nw) x) (uF (Fin.last Nw) x (t₀ + S))) +
    (-1 : ℝ) • truncatePlaneHk (hmc (Fin.last Nw) x) (uk (Fin.last Nw) x (t₀ + S))) 0
      (fun i => i.elim0) z) (Φ x z)
  rw [hz]
  change _ = inner ℝ (planeValue (truncatePlaneHk (hmF (Fin.last Nw) x)
    (uF (Fin.last Nw) x (t₀ + S))) z - planeValue (truncatePlaneHk (hmc (Fin.last Nw) x)
      (uk (Fin.last Nw) x (t₀ + S))) z) (Φ x z)
  rw [planeValue_truncate, planeValue_truncate]
end

end AVRegularity.CycleWords.Seam
end
end
