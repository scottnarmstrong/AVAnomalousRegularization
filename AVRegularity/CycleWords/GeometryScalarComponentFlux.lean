-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
public import AVRegularity.Weighted.FluxCoordinateInjection
import AVRegularity.CycleWords.GeometryScalarCoefficient
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Weighted.WordMomentSlots
public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound

section
public section
namespace AVRegularity.CycleWords

/-! The original Péclet price is at least one at every natural exponent. -/

theorem one_le_peFactor (η : ℝ) : 1 ≤ peFactor η := by
  exact le_add_of_nonneg_right (inv_nonneg.mpr (Real.sqrt_nonneg η))

theorem one_le_peFactor_pow (η : ℝ) (q : ℕ) : 1 ≤ peFactor η ^ q :=
  one_le_pow₀ (one_le_peFactor η)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleWords

/-! Operator-norm word estimates retain the positive path amplitude before cancellation. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D N : ℕ}

omit [DecidableEq ι] in
theorem wordTheta_nonneg_of_admissible (ηg : ℝ) (hηg : 0 ≤ ηg)
    (letters : Fin N → CycleLetter ι h D) (π : ι → ℝ)
    (dom : Set (ℝ × Homogenization.Vec 2)) (J H : ℕ)
    (hL : ∀ i, IsCycleLetter π (letters i) dom J H) : 0 ≤ wordTheta ηg letters := by
  apply Finset.prod_nonneg
  intro i _
  apply mul_nonneg (hL i).theta_nonneg
  split <;> positivity

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! A word coefficient is its diagonal metric plus the actual preceding Taylor letter. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D N : ℕ}

omit [Fintype ι] in
theorem metricFlux_zero {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
    metricFlux (h := h) (0 : Matrix (Fin 2) (Fin 2) ℝ) m hab hm = 0 := by
  subst hab hm
  ext q k
  simp [metricFlux]

theorem wordChainCoefficient_split (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (i i' : Fin (N + 1) × ι)
    (d : admissibleOrders (fun p => κ p.1 p.2) D i i') (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (wordChainData G letters X0 δ) κ i i' d t z =
      (if i.1 = i'.1 then
        (if hv : i.2 = i'.2 ∧ d.1 = 2 then
          metricFlux (G t - 1) (d.1 - 1) hv.1 (by omega) else 0) else 0) +
      (if hs : i.1.val = i'.1.val + 1 then
        slowEvalCoefficient
          (fun f z => taylorSlow (if (letters ⟨i'.1.val, by omega⟩).positive then 1 else 0)
            (letters ⟨i'.1.val, by omega⟩).slow f X0 (δ • z))
          ((letters ⟨i'.1.val, by omega⟩).edge i.2 i'.2
            ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z else 0) := by
  simp [planeChainCoefficient, wordChainData, slowEvalCoefficient, metricFlux_zero]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The literal shear velocity is a transverse Laplace eigenfunction. -/

theorem ocShearVel_component_contDiff {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (hk : Odd k) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ocShearVel α q Λ m k y j) := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have he := funext (fun y => congrFun (CycleReference.ocShearVel_horizontal (α := α) (q := q) (Λ := Λ) (m := m) h1 y) j)
    rw [he]
    fin_cases j <;> dsimp <;> fun_prop
  · have he := funext (fun y => congrFun (CycleReference.ocShearVel_vertical (α := α) (q := q) (Λ := Λ) (m := m) h3 y) j)
    rw [he]
    fin_cases j <;> dsimp <;> fun_prop

theorem ocShearVel_component_laplacian {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (hk : Odd k) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ
      (fun x => ocShearVel α q Λ m k x j) z (basisVec i)) y (basisVec i)) =
      -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 * ocShearVel α q Λ m k y j := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have he := funext (fun y => congrFun (CycleReference.ocShearVel_horizontal (α := α) (q := q) (Λ := Λ) (m := m) h1 y) j)
    rw [he, congrFun he y]
    fin_cases j <;> dsimp
    · simp
    · exact CycleReference.laplacian_cosCoordinate _ _ _ _
  · have he := funext (fun y => congrFun (CycleReference.ocShearVel_vertical (α := α) (q := q) (Λ := Λ) (m := m) h3 y) j)
    rw [he, congrFun he y]
    fin_cases j <;> dsimp
    · exact CycleReference.laplacian_cosCoordinate _ _ _ _
    · simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Replacing row Taylor coefficients by equal cell classes preserves both literal fast parts. -/

theorem fibreFastPart_row_congr_ae
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (he : ∀ p t, ell p t =ᵐ[volume.restrict AVenhance.unitCube] ell' p t)
    (ξ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ) (s t : ℝ) :
    fibreFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreFastPart r lam ell' ξ D s t := by
  have hs := fibreSeriesFun_congr_ae ell ell' he ξ s
  have hi : (∫ y in AVenhance.unitCube, fibreSeriesFun ell ξ s y * cellValue D s y) =
      ∫ y in AVenhance.unitCube, fibreSeriesFun ell' ξ s y * cellValue D s y := by
    apply integral_congr_ae
    filter_upwards [hs] with y hy
    rw [hy]
  exact Filter.Eventually.of_forall (fun x => by unfold fibreFastPart; rw [hi])

theorem fibreAdjointFastPart_row_congr_ae
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (he : ∀ p t, ell p t =ᵐ[volume.restrict AVenhance.unitCube] ell' p t)
    (ξ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ) (s t : ℝ) :
    fibreAdjointFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointFastPart r lam ell' ξ D s t := by
  filter_upwards [fibreSeriesFun_congr_ae ell ell' he ξ s] with x hx
  unfold fibreAdjointFastPart
  rw [hx]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! A fixed output coordinate injection preserves the original constant map norm. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fluxCoordinateInjection_norm_le (k : Fin 2) (T : E →L[ℝ] F) :
    ‖Weighted.fluxCoordinateInjection k T‖ ≤ ‖T‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro e
  have he : Weighted.fluxCoordinateInjection k T e = PiLp.single 2 k (T e) := by
    apply PiLp.ext
    intro j
    by_cases h : j = k
    · subst j
      simp
    · simp [h]
  rw [he, PiLp.norm_single]
  exact T.le_opNorm e

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Exact collapse of the scalar chain's dependent coupling sum to the metric flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The raw coupling flux appearing verbatim in the scalar weak identity. -/
def geometryScalarFlux (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i' : Fin 1 × ι, ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    planeChainCoefficient (geometryScalarData (h := h) D G) κ i i' d t z
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
        (w i').toFunction.jet
          ⟨⟨d.val - 1, by
            have hd := (Finset.mem_filter.mp d.property).2
            dsimp only at hd
            omega⟩, word⟩ z)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The native scalar coupling flux is exactly the diagonal metric deviation times the gradient. -/
theorem geometryScalarFlux_eq (D : ℕ) (hD : 2 ≤ D) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) (k : Fin 2) :
    geometryScalarFlux D G κ w i t z k = ∑ j : Fin 2, (G t z - 1) k j •
      (w i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => j⟩ z := by
  classical
  unfold geometryScalarFlux
  rw [Finset.sum_eq_single i]
  · have hd2 : 2 ∈ admissibleOrders (fun p => κ p.1 p.2) D i i := by
      simp [admissibleOrders, hD]
    let d2 : admissibleOrders (fun p => κ p.1 p.2) D i i := ⟨2, hd2⟩
    rw [Finset.sum_eq_single d2]
    · rw [geometryScalarCoefficient_diagonal D G κ i d2 (by rfl)]
      simp [d2, metricFlux]
    · intro d _ hne
      have hd : d.val ≠ 2 := by
        intro he
        apply hne
        exact Subtype.ext he
      rw [geometryScalarCoefficient_otherOrder D G κ i i d hd t z]
      simp
    · intro hn
      exact False.elim (hn (Finset.mem_univ d2))
  · intro i' _ hne
    have hc : i.2 ≠ i'.2 := by
      intro he
      apply hne
      exact Prod.ext (Subsingleton.elim _ _) he.symm
    apply Finset.sum_eq_zero
    intro d _
    rw [geometryScalarCoefficient_offDiagonal D G κ i i' hc d t z]
    simp
  · intro hn
    exact False.elim (hn (Finset.mem_univ i))
end

/-! The literal chart fiber flux expands into the original identities once per retained order. -/

section
private theorem list_filterMap_map_sum {A B M : Type*} [AddCommMonoid M]
    (l : List A) (f : A → Option B) (g : B → M) :
    ((l.filterMap f).map g).sum = (l.map (fun a => (f a).elim 0 g)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hf : f a <;> simp [hf, ih]

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalCellFiber_slowFlux_expansion (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (d : Finset.Icc 2 D)
    (ev : (Vec 2 → ℝ) → Vec 2 → ℝ) (s t : ℝ) (φ z : Vec 2)
    (g : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) :
    slowEvalCoefficient ev (F.cellFiber s φ p c v u d) t z g =
      ∑ γ : F.Γ v u, if d.1 ≤ (F.identity v u γ).maxOrder then
        ∑ w : DerivativeWord2 (d.1 - 1), ∑ k : Fin 2,
          ev (fun X => F.flux p c v u γ d.1 w (s * t) X (z + φ) k) z •
            Weighted.fluxCoordinateInjection k (F.identity v u γ).map (g w)
      else 0 := by
  classical
  rw [Weighted.slowEvalCoefficient_value_expansion]
  unfold ChartedFamily.cellFiber ConstituentEdges.timeFastShift ChartedFamily.fiber
  rw [List.map_map, list_filterMap_map_sum, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro γ _
  split <;> simp_all only [Option.elim_some, Option.elim_none, Function.comp_apply]
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The actual pulse velocity is the locally finite sum of its literal shear velocities. -/

theorem pulseVelocity_eq_shear_sum {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) (y : Vec 2) (j : Fin 2) :
    streamVel (ocPulseStream α q Λ ζ m) t y j =
      ∑' k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t * ocShearVel α q Λ m k.1 y j := by
  classical
  by_cases ha : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k t ≠ 0
  · obtain ⟨k, hk, hp⟩ := ha
    rw [CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp y]
    change ocPulse α q Λ ζ m k t * ocShearVel α q Λ m k y j = _
    symm
    apply tsum_eq_single (⟨k, hk⟩ : {k : ℤ // Odd k})
    intro l hl
    have hz : ocPulse α q Λ ζ m l.1 t = 0 := by
      by_contra hne
      exact hl (Subtype.ext (CycleReference.odd_pulse_support_unique hΛ hζ l.2 hk hne hp))
    rw [hz, zero_mul]
  · have hp : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t = 0 := by
      intro k hk
      by_contra hne
      exact ha ⟨k, hk, hne⟩
    rw [CycleReference.pulseStreamVel_eq_zero_of_quiet hp y]
    have hz : (fun k : {k : ℤ // Odd k} =>
        ocPulse α q Λ ζ m k.1 t * ocShearVel α q Λ m k.1 y j) = (fun _ => 0) := by
      funext k
      rw [hp k.1 k.2, zero_mul]
    rw [hz, tsum_zero]
    rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! The word chain flux splits into its literal scalar metric and preceding Taylor-letter source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

def wordChainJetArray (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i i' : Fin (N + 1) × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i')
    (z : Vec 2) : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.2) :=
  WithLp.toLp 2 fun word => (U i').toFunction.jet
    ⟨⟨d.1 - 1, by have hd := (Finset.mem_filter.mp d.2).2; dsimp only at hd; omega⟩, word⟩ z

def wordChainRawFlux (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i', ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    planeChainCoefficient (wordChainData G letters X0 δ) κ i i' d t z
      (wordChainJetArray κ U i i' d z)

def wordChainPreviousFlux (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i', ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    (if hs : i.1.val = i'.1.val + 1 then
      slowEvalCoefficient
        (fun f z => taylorSlow (if (letters ⟨i'.1.val, by omega⟩).positive then 1 else 0)
          (letters ⟨i'.1.val, by omega⟩).slow f X0 (δ • z))
        ((letters ⟨i'.1.val, by omega⟩).edge i.2 i'.2
          ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z else 0)
      (wordChainJetArray κ U i i' d z)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem wordChainPreviousFlux_initial (letters : Fin N → CycleLetter ι h D)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (x : ι) (t : ℝ) (z : Vec 2) :
    wordChainPreviousFlux letters X0 δ κ U (0, x) t z = 0 := by
  simp [wordChainPreviousFlux]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem wordChainRawFlux_split (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) :
    wordChainRawFlux G letters X0 δ κ U i t z =
      WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, (G t - 1) k l •
        (U i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) +
      wordChainPreviousFlux letters X0 δ κ U i t z := by
  classical
  let A (i' : Fin (N + 1) × ι)
      (d : admissibleOrders (fun p => κ p.1 p.2) D i i') :=
    (if i.1 = i'.1 then
      (if hv : i.2 = i'.2 ∧ d.1 = 2 then
        metricFlux (G t - 1) (d.1 - 1) hv.1 (by omega) else 0) else 0)
      (wordChainJetArray κ U i i' d z)
  have hs : wordChainRawFlux G letters X0 δ κ U i t z =
      (∑ i', ∑ d, A i' d) + wordChainPreviousFlux letters X0 δ κ U i t z := by
    unfold wordChainRawFlux wordChainPreviousFlux
    simp_rw [wordChainCoefficient_split, add_apply]
    simp only [Finset.sum_add_distrib, A]
  rw [hs]
  congr 1
  rw [Finset.sum_eq_single i]
  · have hd2 : 2 ∈ admissibleOrders (fun p => κ p.1 p.2) D i i := by
      simp [admissibleOrders, hD]
    let d2 : admissibleOrders (fun p => κ p.1 p.2) D i i := ⟨2, hd2⟩
    rw [Finset.sum_eq_single d2]
    · apply PiLp.ext
      intro k
      simp [A, d2, metricFlux, wordChainJetArray]
    · intro d _ hne
      have hd : d.1 ≠ 2 := fun he => hne (Subtype.ext he)
      simp [A, hd]
    · intro hn
      exact False.elim (hn (Finset.mem_univ d2))
  · intro i' _ hne
    apply Finset.sum_eq_zero
    intro d _
    by_cases hj : i.1 = i'.1
    · have hu : i.2 ≠ i'.2 := fun he => hne (Prod.ext hj he).symm
      simp [A, hj, hu]
    · simp [A, hj]
  · intro hn
    exact False.elim (hn (Finset.mem_univ i))

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleWords

/-! A decreasing fixed Sobolev reserve preserves every originally admitted source edge. -/

def wordSobolevReserve {N : ℕ} (K : ℕ) (d : Fin N → ℕ) (j : Fin (N + 1)) : ℕ :=
  Weighted.wordMomentSlot K (fun i => d i - 2) j

def cappedWordSlots {ι : Type*} {N : ℕ} (κ : Fin (N + 1) → ι → ℕ)
    (K : ℕ) (d : Fin N → ℕ) (j : Fin (N + 1)) (x : ι) : ℕ :=
  min (κ j x) (wordSobolevReserve K d j)

theorem wordSobolevReserve_castSucc {N : ℕ} (K : ℕ) (d : Fin N → ℕ) (j : Fin N) :
    wordSobolevReserve K d j.castSucc = wordSobolevReserve K d j.succ + (d j - 2) :=
  Weighted.wordMomentSlot_castSucc K (fun i => d i - 2) j

theorem wordSobolevReserve_le {N : ℕ} (K : ℕ) (d : Fin N → ℕ) (j : Fin (N + 1)) :
    wordSobolevReserve K d j ≤ K + ∑ i, d i := by
  unfold wordSobolevReserve Weighted.wordMomentSlot
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact Nat.sub_le _ _
  · exact Nat.zero_le _

theorem wordSobolevReserve_last {N : ℕ} (K : ℕ) (d : Fin N → ℕ) :
    wordSobolevReserve K d (Fin.last N) = K := by
  have he (i : Fin N) : ¬ N ≤ i.val := Nat.not_le.mpr i.isLt
  simp only [wordSobolevReserve, Weighted.wordMomentSlot, Fin.val_last, he,
    ite_false, Finset.sum_const_zero, Nat.add_zero]

theorem cappedWordSlots_le_original {ι : Type*} {N : ℕ} (κ : Fin (N + 1) → ι → ℕ)
    (K : ℕ) (d : Fin N → ℕ) (j : Fin (N + 1)) (x : ι) :
    cappedWordSlots κ K d j x ≤ κ j x := Nat.min_le_left _ _

theorem cappedWordSlots_le_fixed {ι : Type*} {N : ℕ} (κ : Fin (N + 1) → ι → ℕ)
    (K : ℕ) (d : Fin N → ℕ) (j : Fin (N + 1)) (x : ι) :
    cappedWordSlots κ K d j x ≤ K + ∑ i, d i :=
  (Nat.min_le_right _ _).trans (wordSobolevReserve_le K d j)

theorem cappedWordSlots_edge_compatible {ι : Type*} {N : ℕ}
    (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    (j : Fin N) (x y : ι) (o : ℕ) (ho : 2 ≤ o) (hod : o ≤ d j)
    (hκ : κ j.succ x + o ≤ κ j.castSucc y + 2) :
    cappedWordSlots κ K d j.succ x + o ≤ cappedWordSlots κ K d j.castSucc y + 2 := by
  unfold cappedWordSlots
  rw [wordSobolevReserve_castSucc]
  omega

theorem cappedWordSlots_last {ι : Type*} {N : ℕ} (κ : Fin (N + 1) → ι → ℕ)
    (K : ℕ) (d : Fin N → ℕ) (x : ι) (hx : K ≤ κ (Fin.last N) x) :
    cappedWordSlots κ K d (Fin.last N) x = K := by
  rw [cappedWordSlots, wordSobolevReserve_last, Nat.min_eq_right hx]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology
namespace AVRegularity.CycleWords

/-! Native H1 test moments separate arbitrary cell L2 states. -/

theorem cellL2_eq_of_H1_pairings (u v : ComplexCellL2)
    (h : ∀ z : TorusHk 1 ℂ, inner ℝ u (torusHkValueCLM z) = inner ℝ v (torusHkValueCLM z)) :
    u = v := by
  let d := u - v
  have hz (N : ℕ) : inner ℝ d (cellGalerkinValue N (cellGalerkinL2Initial N d)) = 0 := by
    change inner ℝ (u - v) (torusHkValueCLM (cellGalerkinL2Initial N d).val) = 0
    rw [inner_sub_left, h, sub_self]
  have hl : Tendsto (fun N => inner ℝ d (cellGalerkinValue N (cellGalerkinL2Initial N d)))
      atTop (𝓝 (inner ℝ d d)) :=
    (tendsto_const_nhds (x := d)).inner (cellGalerkinL2Initial_tendsto d)
  have he : inner ℝ d d = 0 :=
    tendsto_nhds_unique hl (by simpa only [hz] using (tendsto_const_nhds (x := (0 : ℝ))))
  have hd : d = 0 := inner_self_eq_zero.mp he
  exact sub_eq_zero.mp hd

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Scalar metric fluxes agree when a component is indexed by a singleton. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryScalar_component_flux (D : ℕ) (hD : 2 ≤ D)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (K : ι → ℕ)
    (U : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)) (x : ι) :
    (fun r => geometryScalarFlux D G (fun _ u => K u) (fun q => U q.2 r) (0, x) r) =
    (fun r => geometryScalarFlux (h := fun _ : Unit => h x) D G
      (fun _ _ => K x) (fun _ => U x r) (0, ()) r) := by
  funext r z
  apply PiLp.ext
  intro k
  rw [geometryScalarFlux_eq D hD, geometryScalarFlux_eq D hD]

end AVRegularity.CycleWords
end
end
