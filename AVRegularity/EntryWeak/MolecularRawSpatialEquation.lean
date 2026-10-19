-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.PrimitiveShearWindowBound
import AVRegularity.CoupledEnergy.Variational.TorusRawSpatialForm
public import AVRegularity.CycleComparison.Lift.SettingInverseZero
public import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries
import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Symmetry of the actual molecular metric follows directly from its Gram formula. -/

theorem actual_family_metric_symmetric (D : OCData) (A : RealChain) (t : ℝ)
    (i j : Fin 2) : A.famMetric D t i j = A.famMetric D t j i := by
  have hs := Matrix.isSymm_mul_transpose_self ((A.famJac D t)⁻¹)
  exact hs.apply j i

theorem familyLiftData_metric_symmetric {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (m : ℕ) (slot : ℤ) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm h) (t : ℝ) (X : Vec 2) (i j : Fin 2) :
    (familyLiftData D m slot A ρ edge).G t X i j =
      (familyLiftData D m slot A ρ edge).G t X j i :=
  actual_family_metric_symmetric D (A.recenter D (ρ • X)) (D.cellScaleSq m * t) i j

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Higher carrier readouts preserve the literal raw subtraction and scaling. -/

theorem higherCarrier_sub_raw_value_ae (K : ℕ) (u v : TorusHk K ℂ)
    (D E : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hu : torusHkValueCLM u =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hv : torusHkValueCLM v =ᵐ[volume.restrict AVenhance.unitCube] cellValue E t) :
    torusHkValueCLM (u - v) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (D - E) t := by
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (torusHkValueCLM u) (torusHkValueCLM v), hu, hv] with x hx hux hvx
  change _ = D t (valueIndex2 1) x - E t (valueIndex2 1) x
  simpa only [Pi.sub_apply, cellValue, hux, hvx] using hx

theorem higherCarrier_smul_raw_value_ae (K : ℕ) (u : TorusHk K ℂ)
    (D : ℝ → RawJet2 1 ℂ) (t r : ℝ)
    (hu : torusHkValueCLM u =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    torusHkValueCLM (r • u) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r • D) t := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul r (torusHkValueCLM u), hu] with x hx hux
  change _ = r • D t (valueIndex2 1) x
  simpa only [Pi.smul_apply, cellValue, hux] using hx

theorem higherCarrier_norm_le_of_raw_value (K : ℕ) (u : TorusHk K ℂ)
    (D : ℝ → RawJet2 1 ℂ) (t R : ℝ)
    (hu : torusHkValueCLM u =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hq : ∃ q : TorusHk K ℂ, ‖q‖ ≤ R ∧
      torusHkValueCLM q =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) : ‖u‖ ≤ R := by
  obtain ⟨q, hb, he⟩ := hq
  have heq : u = q := by
    apply TorusHk.ext_value
    exact Lp.ext (hu.trans he.symm)
  rw [heq]
  exact hb

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Constituent and lift coefficient germs determine the full finite source-flux terms locally. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set (Vec 2)}

theorem constituentLeftTerms_slow_local_congr (hU : IsOpen U) (η : ℝ) (w : List (Fin 2))
    (j : ℕ) (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq U) l r)
    (T : F →L[ℝ] G) (a : Vec 2 → Vec 2 → ℝ) :
    List.Forall₂ (LeftTermSlowEq U) (constituentLeftTerms η w j l T a)
      (constituentLeftTerms η w j r T a) :=
  List.rel_map (fun _ _ h => h.fieldSmul a)
    (List.rel_map (fun _ _ h => h.postcompose T)
      (covariantLeftTermList_slow_local_congr hU η w l r he j))

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem leftTermSlowEq_flatMap_same {A : Type*} (l : List A)
    (f g : A → List (LeftTerm E F))
    (he : ∀ a ∈ l, List.Forall₂ (LeftTermSlowEq U) (f a) (g a)) :
    List.Forall₂ (LeftTermSlowEq U) (l.flatMap f) (l.flatMap g) := by
  have hl : List.Forall₂ (fun a b => a = b ∧ a ∈ l) l l :=
    List.forall₂_same.mpr (fun a ha => ⟨rfl, ha⟩)
  exact List.rel_flatMap hl (fun a b hab => by rcases hab with ⟨rfl, ha⟩; exact he a ha)

variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {D : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem liftComponentLeftTerms_slow_local_congr (n : ℕ) (c d : LiftCoeff ι hv) (t : ℝ) (v : ι)
    (he : ∀ m ≤ n, ∀ α X, X ∈ U → ∀ z u, c m α t X z v u = d m α t X z v u) :
    List.Forall₂ (LeftTermSlowEq U) (liftComponentLeftTerms n c t v) (liftComponentLeftTerms n d t v) := by
  unfold liftComponentLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro m hm
  apply leftTermSlowEq_flatMap_same
  intro α _
  refine List.rel_map ?_ (List.forall₂_refl (Rₐ := Eq) (Finset.univ.toList : List ι))
  intro u u' hu
  subst u'
  refine ⟨rfl, HEq.rfl, ?_⟩
  intro X hX z
  exact congrArg (fun f => f.comp (ContinuousLinearMap.proj u))
    (he m (by have h := Finset.mem_range.mp (Finset.mem_toList.mp hm); omega) α X hX z u)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem sourceFluxLeftTerms_slow_local_congr (hU : IsOpen U)
    (edge : ConstituentEdges D hv) (η t : ℝ) (n : ℕ) (c d : LiftCoeff ι hv)
    (k : Fin 2) (j : ℕ) (v : ι)
    (he : ∀ m ≤ n, ∀ α X, X ∈ U → ∀ z u u', c m α t X z u u' = d m α t X z u u') :
    List.Forall₂ (LeftTermSlowEq U) (sourceFluxLeftTerms edge η t n c k j v)
      (sourceFluxLeftTerms edge η t n d k j v) := by
  unfold sourceFluxLeftTerms
  apply leftTermSlowEq_flatMap_same
  intro u _
  apply leftTermSlowEq_flatMap_same
  intro e _
  apply leftTermSlowEq_flatMap_same
  intro γ _
  apply leftTermSlowEq_flatMap_same
  intro α _
  exact constituentLeftTerms_slow_local_congr hU η (List.ofFn α) j _ _
    (liftComponentLeftTerms_slow_local_congr n c d t u (fun m hm α X hX z u' => he m hm α X hX z u u'))
    γ.map (fun X z => γ.coeff α t X z k)
end

/-! Local constituent replacements preserve the finite differential terms of native means. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {U : Set (Vec 2)}

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem LeftTermSlowEq.fieldSmul_congr {c d : LeftTerm E F}
    (he : LeftTermSlowEq U c d) {a b : Vec 2 → Vec 2 → ℝ}
    (hab : SlowOpenFieldEq U a b) :
    LeftTermSlowEq U (c.fieldSmul a) (d.fieldSmul b) := by
  refine ⟨he.order, he.word, ?_⟩
  intro X hX z
  exact congrArg₂ (fun r : ℝ => fun f : E →L[ℝ] F => r • f)
    (hab X hX z) (he.coeff X hX z)

theorem constituentLeftTerms_slow_local_replacement (hU : IsOpen U)
    (η : ℝ) (w : List (Fin 2)) (j : ℕ)
    (l r : List (LeftTerm E F)) (he : List.Forall₂ (LeftTermSlowEq U) l r)
    (T T' : F →L[ℝ] G) (hT : T = T')
    (a b : Vec 2 → Vec 2 → ℝ) (hab : SlowOpenFieldEq U a b) :
    List.Forall₂ (LeftTermSlowEq U) (constituentLeftTerms η w j l T a)
      (constituentLeftTerms η w j r T' b) := by
  subst T'
  exact List.rel_map (fun _ _ h => h.fieldSmul_congr hab)
    (List.rel_map (fun _ _ h => h.postcompose T)
      (covariantLeftTermList_slow_local_congr hU η w l r he j))
end

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Integrable complex spatial expressions for every H¹ test of the cell equation. -/

/-- The complex cell spatial expression written with class representatives. -/
def dataComplexSpatial (P : MolecularData)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (x : Vec 2) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2,
    dataMetricEntryCLM P t j k (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u) x *
      star (cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) k z x)) -
  (∑ j : Fin 2, cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable P.drift_bounded t j (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u) x *
    star (torusHkValueCLM z x)) +
  cellScalarCLM (0 : ℂ) (torusHkValueCLM u) x * star (torusHkValueCLM z x) +
  S x * star (torusHkValueCLM z x) - ∑ j : Fin 2,
    F j x * star (cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j z x)

/-- Every term is a product of two L² classes, so the literal complex expression is integrable. -/
theorem dataComplexSpatial_integrable (P : MolecularData)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    Integrable (dataComplexSpatial P t u z S F) (volume.restrict AVenhance.unitCube) := by
  have hm := integrable_finsetSum' Finset.univ (fun j _ =>
    integrable_finsetSum' Finset.univ (fun k _ => cellComplex_pairing_integrable
      (dataMetricEntryCLM P t j k (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u))
      (cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) k z)))
  have hd := integrable_finsetSum' Finset.univ (fun j _ => cellComplex_pairing_integrable
    (cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable P.drift_bounded t j (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u)) (torusHkValueCLM z))
  have hp := cellComplex_pairing_integrable (cellScalarCLM (0 : ℂ) (torusHkValueCLM u)) (torusHkValueCLM z)
  have hs := cellComplex_pairing_integrable S (torusHkValueCLM z)
  have hf := integrable_finsetSum' Finset.univ (fun j _ => cellComplex_pairing_integrable (F j)
    (cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j z))
  have hi := ((hm.neg.sub hd).add hp).add hs |>.sub hf
  apply hi.congr
  filter_upwards with x
  simp only [dataComplexSpatial, Finset.sum_apply, Pi.neg_apply, Pi.sub_apply, Pi.add_apply]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Continuous dependence of the integrated generator functional on its H¹ test. -/

/-- The integrated generator formula also applies to the canonical temporal class representative. -/
theorem dataGeneratorIntegralCLM_apply_class {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (P : MolecularData)
    (z : TorusHk 1 ℂ)
    (U : CellBochnerH1 a b) :
    dataGeneratorIntegralCLM a b s t P z U =
      ∫ r in s..t, dataGeneratorForm P r (U r) z := by
  simpa only [Lp.toLp_coeFn] using
    dataGeneratorIntegralCLM_apply hs ht hst P z U (Lp.memLp U)

/-- Actual generator entries against a Bochner H¹ state are integrable on subintervals. -/
theorem dataGenerator_pairing_intervalIntegrable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (P : MolecularData)
    (z : TorusHk 1 ℂ)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun r => dataGeneratorForm P r (u r) z) volume s t := by
  simpa only [dataGeneratorTest_pairing] using cellTime_inner_intervalIntegrable hs ht hst
    u (fun r => dataGeneratorTest P r z) hu
    (dataGeneratorTest_memLp a b P z)

/-- The integrated generator is linear in its fixed H¹ test. -/
def dataGeneratorIntegralTestLinearMap {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (P : MolecularData)
    :
    TorusHk 1 ℂ →ₗ[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) where
  toFun z := dataGeneratorIntegralCLM a b s t P z
  map_add' z w := by
    ext U
    simp only [add_apply, dataGeneratorIntegralCLM_apply_class hs ht hst]
    have he : (fun r => dataGeneratorForm P r (U r) (z + w)) =
        fun r => dataGeneratorForm P r (U r) z + dataGeneratorForm P r (U r) w := by
      funext r
      exact (dataGeneratorForm P r (U r)).map_add z w
    rw [he]
    exact intervalIntegral.integral_add
      (dataGenerator_pairing_intervalIntegrable hs ht hst P z U (Lp.memLp U))
      (dataGenerator_pairing_intervalIntegrable hs ht hst P w U (Lp.memLp U))
  map_smul' r z := by
    ext U
    simp only [smul_apply, dataGeneratorIntegralCLM_apply_class hs ht hst]
    simp_rw [map_smul, smul_eq_mul]
    exact intervalIntegral.integral_const_mul r _

/-- Continuous dependence on the fixed test in the temporal dual norm. -/
def dataGeneratorIntegralTestCLM {a b s t : ℝ} (hab : a ≤ b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (P : MolecularData)
    :
    TorusHk 1 ℂ →L[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) :=
  by
    let h := dataGeneratorIntegralCLM_uniform_norm_bound hab P
    let L : TorusHk 1 ℂ →ₗ[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) :=
      dataGeneratorIntegralTestLinearMap hs ht hst P
    refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := TorusHk 1 ℂ)
      (F := CellBochnerH1 a b →L[ℝ] ℝ) (σ := RingHom.id ℝ) L h.choose ?_
    intro z
    change ‖dataGeneratorIntegralCLM a b s t P z‖ ≤ h.choose * ‖z‖
    exact h.choose_spec.2 s t z

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Every drift in the weak inverse statement supplies the existing cell drift predicate. -/

theorem scaled_drift_isCellDrift (l : ℕ) (v : ℝ → Vec 2 → Vec 2) (Cv Pe : ℝ)
    (hm : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hv : ∀ t, ContDiff ℝ ((l + 1 : ℕ) : ℕ∞) (v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (v t))
    (hb : ∀ t (j : ℕ), j ≤ l + 1 → ∀ z, ‖iteratedFDeriv ℝ j (v t) z‖ ≤ Cv)
    (hd : ∀ t z, ∑ i : Fin 2, fderiv ℝ (fun z' => v t z' i) z (Pi.single i 1) = 0) :
    IsCellDrift (fun t z => Pe • v t z) := by
  refine ⟨hm.const_smul Pe, ⟨2 * Pe * Cv, scaled_drift_square_bound l v Cv Pe hb⟩,
    ?_, ?_⟩
  · intro t n z
    exact congrArg (fun w : Vec 2 => Pe • w) (hp t n z)
  · intro t ψ
    have hv1 : ContDiff ℝ 1 (v t) := (hv t).of_le (by simp)
    have hz := classical_divergence_free_weak (v t) (fun i => contDiff_pi.mp hv1 i)
      (fun i n z => congrArg (fun f : Vec 2 => f i) (hp t n z))
      (by simpa only [basisVec] using hd t) ψ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [integral_const_mul, hz, mul_zero]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Higher Sobolev energy bounds use molecular coercivity and the proved finite multiplier. -/

theorem factorialPairing_abs_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (ρ : ℝ) (u z : TorusHk K E) :
    |inner ℝ (factorialWeightedJet ρ u.val) (factorialWeightedJet ρ z.val)| ≤
      Real.sqrt (factorialNormSq ρ u.val) * Real.sqrt (factorialNormSq ρ z.val) := by
  have hn (w : TorusHk K E) : ‖factorialWeightedJet ρ w.val‖ =
      Real.sqrt (factorialNormSq ρ w.val) := by
    rw [← factorialWeightedJet_normSq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hn] using abs_real_inner_le_norm (factorialWeightedJet ρ u.val)
    (factorialWeightedJet ρ z.val)

theorem dataHigher_spatial_energy_bound (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j)
    (t : ℝ) (v : Vec 2 → Vec 2) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) v) (hp : AVenhance.IsZ2Periodic v)
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (u S : TorusHk K ℂ) (w : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) :
    2 * (-dataHigherDiffusion K ρ G t w -
      inner ℝ (factorialWeightedJet ρ (finiteTransport K v Cv hCv hv hp hb w).val)
        (factorialWeightedJet ρ u.val) +
      inner ℝ (factorialWeightedJet ρ S.val) (factorialWeightedJet ρ u.val)) +
      factorialNormSq ρ w.val ≤
      (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
        finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * factorialNormSq ρ u.val +
        factorialNormSq ρ S.val := by
  let B := ∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
    finiteTransportBudget (E := ℂ) K Cv j
  let U := Real.sqrt (factorialNormSq ρ u.val)
  let W := Real.sqrt (factorialNormSq ρ w.val)
  let F := Real.sqrt (factorialNormSq ρ S.val)
  have hD := dataHigherDiffusion_coercive K ρ G hG t w
  have hT := (factorialPairing_abs_le ρ (finiteTransport K v Cv hCv hv hp hb w) u).trans
    (mul_le_mul_of_nonneg_right (finiteTransport_factorialNorm_le K v Cv hCv hv hp hb w ρ hρ)
      (Real.sqrt_nonneg _))
  have hS := factorialPairing_abs_le ρ S u
  have hU : U ^ 2 = factorialNormSq ρ u.val := Real.sq_sqrt (factorialNormSq_nonneg _ _)
  have hW : W ^ 2 = factorialNormSq ρ w.val := Real.sq_sqrt (factorialNormSq_nonneg _ _)
  have hF : F ^ 2 = factorialNormSq ρ S.val := Real.sq_sqrt (factorialNormSq_nonneg _ _)
  change |inner ℝ _ _| ≤ B * W * U at hT
  change |inner ℝ _ _| ≤ F * U at hS
  exact higherEnergy_arithmetic _ _ _ _ _ _ B U W F hD hT hS hU hW hF

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Component cross forcings use scalar reserves; whole-family regularity supplies only the projection identity. -/

variable {ι : Type*} [Fintype ι]

theorem normalizedCellB1Source_component (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : ∀ u, JointSourceReserve (H + 2) (fun t z Y => f t z Y u))
    (t : ℝ) (z Y : Vec 2) (u : ι) :
    normalizedCellB1Source A η G v (fun t z Y => f t z Y u) t z Y =
      normalizedCellB1Source A η G v f t z Y u := by
  classical
  let Qwhole := jointSourcePiReserve (H + 2) (fun u t z Y => f t z Y u) Qf
  have hb : IsBoxSmooth 1 1 (fun X y => Real.exp (A X) • f t y X) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      (((Qwhole.exponentialGoodField A t).mono (by omega : 1 + 1 ≤ H + 2)).1)
  have hG (i j : Fin 2) : IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      ((((QG i j).goodField t).mono (by omega : 1 + 0 ≤ H + 1)).1)
  have he := cellB1_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u) η G v t _ hb hG Y z
  simpa only [normalizedCellB1Source, Pi.smul_apply, ContinuousLinearMap.proj_apply] using
    congrArg (fun x : ℝ => (Real.exp (A Y))⁻¹ • x) he

theorem normalizedCellB2Source_component (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (f : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : ∀ u, JointSourceReserve (H + 2) (fun t z Y => f t z Y u))
    (t : ℝ) (z Y : Vec 2) (u : ι) :
    normalizedCellB2Source A η G (fun t z Y => f t z Y u) t z Y =
      normalizedCellB2Source A η G f t z Y u := by
  classical
  let Qwhole := jointSourcePiReserve (H + 2) (fun u t z Y => f t z Y u) Qf
  have hb : IsBoxSmooth 2 0 (fun X y => Real.exp (A X) • f t y X) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      (((Qwhole.exponentialGoodField A t).mono (by omega : 2 + 0 ≤ H + 2)).1)
  have hG (i j : Fin 2) : IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      ((((QG i j).goodField t).mono (by omega : 1 + 0 ≤ H + 1)).1)
  have he := cellB2_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u) η G t _ hb hG Y z
  simpa only [normalizedCellB2Source, Pi.smul_apply, ContinuousLinearMap.proj_apply] using
    congrArg (fun x : ℝ => (Real.exp (A Y))⁻¹ • x) he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The vector derivative bounds control every scaled drift component. -/

theorem scaled_drift_component_bound (l : ℕ) (v : ℝ → Vec 2 → Vec 2) (Cv Pe : ℝ)
    (hv : ∀ t, ContDiff ℝ ((l + 1 : ℕ) : ℕ∞) (v t))
    (hb : ∀ t j, j ≤ l + 1 → ∀ x, ‖iteratedFDeriv ℝ j (v t) x‖ ≤ Cv) :
    ∀ t j, j ≤ l → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun y => (Pe • v t y) k) x‖ ≤ |Pe| * Cv := by
  intro t j hj k x
  let L : Vec 2 →L[ℝ] ℝ := Pe • ContinuousLinearMap.proj k
  have hL : ‖L‖ ≤ |Pe| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
    intro z
    change ‖Pe * z k‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z k) (abs_nonneg Pe)
  change ‖iteratedFDeriv ℝ j (L ∘ v t) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hv t).contDiffAt (by exact_mod_cast (by omega : j ≤ l + 1))]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul hL (hb t j (by omega) x) (norm_nonneg _) (abs_nonneg Pe))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Slow difference quotients of genuine joint sources have higher carriers with a uniform budget. -/

def sourceSlowQuotient {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℝ → Vec 2 → Vec 2 → E) (Y v : Vec 2) (h : ℝ) : ℝ → Vec 2 → E :=
  fun t z => h⁻¹ • (f t z (Y + h • v) - f t z Y)

def slowQuotientHigherSourceData (a b : ℝ) (K : ℕ)
    (src : ℝ → Vec 2 → Vec 2 → ℂ)
    (flux : ℝ → Vec 2 → Vec 2 → ComplexCellVector)
    (hs : ∀ t, ContDiff ℝ ((K + 1 : ℕ) : ℕ∞)
      (fun X : Vec 2 × Vec 2 => src t X.1 X.2))
    (hf : ∀ t, ContDiff ℝ ((K + 1 : ℕ) : ℕ∞)
      (fun X : Vec 2 × Vec 2 => flux t X.1 X.2))
    (hps : ∀ t Y, AVenhance.IsZ2Periodic (fun z => src t z Y))
    (hpf : ∀ t Y, AVenhance.IsZ2Periodic (fun z => flux t z Y))
    (hms : ∀ Y, Measurable (fun a : ℝ × Vec 2 => src a.1 a.2 Y))
    (hmf : ∀ Y, Measurable (fun a : ℝ × Vec 2 => flux a.1 a.2 Y))
    (Cs Cf : ℕ → ℝ) (hCs : ∀ n, 0 ≤ Cs n) (hCf : ∀ n, 0 ≤ Cf n)
    (hbs : ∀ n, n ≤ K + 1 → ∀ t X,
      ‖iteratedFDeriv ℝ n (fun X : Vec 2 × Vec 2 => src t X.1 X.2) X‖ ≤ Cs n)
    (hbf : ∀ n, n ≤ K + 1 → ∀ t X,
      ‖iteratedFDeriv ℝ n (fun X : Vec 2 × Vec 2 => flux t X.1 X.2) X‖ ≤ Cf n)
    (Y v : Vec 2) (h : ℝ) (hh : h ≠ 0) :
    HigherSourceCarrierData (Set.Icc a b) K
      (fun t => cellQ0 (sourceSlowQuotient src Y v h t)) (sourceSlowQuotient flux Y v h) :=
  finiteMeanFreeHigherSourceData a b K (sourceSlowQuotient src Y v h)
    (sourceSlowQuotient flux Y v h)
    (fun t => (((hs t).of_le (by exact_mod_cast (Nat.le_succ K))).comp₂
      contDiff_id contDiff_const |>.sub
      (((hs t).of_le (by exact_mod_cast (Nat.le_succ K))).comp₂
        contDiff_id contDiff_const)).const_smul h⁻¹)
    (fun t => (((hf t).of_le (by exact_mod_cast (Nat.le_succ K))).comp₂
      contDiff_id contDiff_const |>.sub
      (((hf t).of_le (by exact_mod_cast (Nat.le_succ K))).comp₂
        contDiff_id contDiff_const)).const_smul h⁻¹)
    (fun t k z => by simp only [sourceSlowQuotient, hps t (Y + h • v) k z, hps t Y k z])
    (fun t k z => by simp only [sourceSlowQuotient, hpf t (Y + h • v) k z, hpf t Y k z])
    (((hms (Y + h • v)).sub (hms Y)).const_smul h⁻¹)
    (((hmf (Y + h • v)).sub (hmf Y)).const_smul h⁻¹)
    (fun n => Cs (n + 1) * ‖v‖) (fun n => Cf (n + 1) * ‖v‖)
    (fun n => mul_nonneg (hCs _) (norm_nonneg v))
    (fun n => mul_nonneg (hCf _) (norm_nonneg v))
    (fun n hn t z => joint_fast_quotient_derivative_bound n
      (fun X : Vec 2 × Vec 2 => src t X.1 X.2)
      ((hs t).of_le (by exact_mod_cast (show n + 1 ≤ K + 1 by omega)))
      (Cs (n + 1)) (hbs _ (by omega) t) Y v z h hh)
    (fun n hn t z => joint_fast_quotient_derivative_bound n
      (fun X : Vec 2 × Vec 2 => flux t X.1 X.2)
      ((hf t).of_le (by exact_mod_cast (show n + 1 ≤ K + 1 by omega)))
      (Cf (n + 1)) (hbf _ (by omega) t) Y v z h hh)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Produced higher quotient carriers upgrade a genuine energy derivative to a classical fast-jet derivative. -/

theorem classical_fast_jet_derivative_of_energy_quotients (K n : ℕ) (hn : n + 4 ≤ K)
    (u : ℝ → TorusHk K ℂ) (v : TorusHk K ℂ)
    (D : ℝ → ℝ → RawJet2 1 ℂ) (E : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hu : ∀ h, torusHkValueCLM (u h) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (D h) t)
    (hv : torusHkValueCLM v =ᵐ[volume.restrict AVenhance.unitCube] cellValue E t)
    (he : Tendsto (fun h : ℝ => cellEnergyNorm Set.univ
      (h⁻¹ • (D h - D 0) - E)) (𝓝[≠] 0) (𝓝 0))
    (R : ℝ) (hq : ∀ h : ℝ, h ≠ 0 → ∃ q : TorusHk K ℂ, ‖q‖ ≤ R ∧
      torusHkValueCLM q =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (h⁻¹ • (D h - D 0)) t)
    (z : Vec 2) :
    HasDerivAt (fun h => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (u h))) z)
      (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z) 0 := by
  have hread (h : ℝ) : torusHkValueCLM (h⁻¹ • (u h - u 0) - v) =ᵐ[
      volume.restrict AVenhance.unitCube] cellValue (h⁻¹ • (D h - D 0) - E) t :=
    higherCarrier_sub_raw_value_ae K _ _ _ E t
      (higherCarrier_smul_raw_value_ae K _ _ t h⁻¹
        (higherCarrier_sub_raw_value_ae K _ _ _ _ t (hu h) (hu 0))) hv
  have ht := carrier_value_tendsto_zero_of_raw_energy (𝓝[≠] (0 : ℝ)) K
    (fun h => h⁻¹ • (u h - u 0) - v) (fun h => h⁻¹ • (D h - D 0) - E) t hread he
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h⁻¹ • (u h - u 0) - v‖ ≤ R + ‖v‖ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := hh
    have hnorm : ‖h⁻¹ • (u h - u 0)‖ ≤ R :=
      higherCarrier_norm_le_of_raw_value K _ _ t R
        (higherCarrier_smul_raw_value_ae K _ _ t h⁻¹
          (higherCarrier_sub_raw_value_ae K _ _ _ _ t (hu h) (hu 0))) (hq h hne)
    exact (norm_sub_le _ _).trans (add_le_add hnorm (le_refl ‖v‖))
  exact higher_carrier_real_jet_hasDerivAt K n hn u v ht (R + ‖v‖) hb z

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Actual high molecular energy with scalar and regular divergence forcing. -/

/-- Conditional spatial estimate: mean-free Poincaré control and the small
transport budget are stated explicitly, rather than hidden in the constant. -/
theorem dataHigher_spatial_flux_energy_small_transport (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j)
    (t : ℝ) (v : Vec 2 → Vec 2) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) v) (hp : AVenhance.IsZ2Periodic v)
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (u S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) (w : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hP : factorialNormSq ρ u.val ≤ factorialNormSq ρ w.val)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8) :
    2 * (-dataHigherDiffusion K ρ G t w -
      inner ℝ (factorialWeightedJet ρ (finiteTransport K v Cv hCv hv hp hb w).val)
        (factorialWeightedJet ρ u.val) +
      inner ℝ (factorialWeightedJet ρ S.val) (factorialWeightedJet ρ u.val) -
      inner ℝ (factorialWeightedJet ρ F.val) (factorialWeightedJet ρ w.val)) +
      factorialNormSq ρ w.val / 2 ≤ 4 * (factorialNormSq ρ S.val + factorialNormSq ρ F.val) := by
  let B := ∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
    finiteTransportBudget (E := ℂ) K Cv j
  have hT := (factorialPairing_abs_le ρ (finiteTransport K v Cv hCv hv hp hb w) u).trans
    (mul_le_mul_of_nonneg_right (finiteTransport_factorialNorm_le K v Cv hCv hv hp hb w ρ hρ)
      (Real.sqrt_nonneg _))
  change |inner ℝ _ _| ≤ B * Real.sqrt (factorialNormSq ρ w.val) *
    Real.sqrt (factorialNormSq ρ u.val) at hT
  exact smallTransportFluxEnergy_arithmetic _ _ _ _ _ _ _ _ B _ _ _ _
    (dataHigherDiffusion_coercive K ρ G hG t w) hT (factorialPairing_abs_le ρ S u) (factorialPairing_abs_le ρ F w)
    (Real.sq_sqrt (factorialNormSq_nonneg _ _))
    (Real.sq_sqrt (factorialNormSq_nonneg _ _))
    (Real.sq_sqrt (factorialNormSq_nonneg _ _))
    (Real.sq_sqrt (factorialNormSq_nonneg _ _))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hP) hsmall

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Mean subtraction commutes exactly with the genuine slow source quotient. -/

theorem source_mean_free_quotient_eq (f : ℝ → Vec 2 → Vec 2 → ℂ)
    (hf : ∀ t Y, MemLp (fun z => f t z Y) 2 (volume.restrict AVenhance.unitCube))
    (Y v : Vec 2) (h : ℝ) :
    (fun t => cellQ0 (sourceSlowQuotient f Y v h t)) =
      h⁻¹ • ((fun t => cellQ0 (fun z => f t z (Y + h • v))) -
        (fun t => cellQ0 (fun z => f t z Y))) := by
  funext t
  change cellQ0 (h⁻¹ • ((fun z => f t z (Y + h • v)) - (fun z => f t z Y))) = _
  rw [cellQ0_smul, cellQ0_sub _ _ (hf t (Y + h • v)) (hf t Y)]
  rfl

def meanFreeQuotientHigherSourceData (a b : ℝ) (K : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → Vec 2 → ComplexCellVector)
    (hf : ∀ t Y, MemLp (fun z => f t z Y) 2 (volume.restrict AVenhance.unitCube))
    (Y v : Vec 2) (h : ℝ)
    (Q : HigherSourceCarrierData (Set.Icc a b) K
      (fun t => cellQ0 (sourceSlowQuotient f Y v h t)) (sourceSlowQuotient F Y v h)) :
    HigherSourceCarrierData (Set.Icc a b) K
      (h⁻¹ • ((fun t => cellQ0 (fun z => f t z (Y + h • v))) -
        (fun t => cellQ0 (fun z => f t z Y))))
      (h⁻¹ • ((fun t z => F t z (Y + h • v)) - (fun t z => F t z Y))) :=
  Q.of_eq (source_mean_free_quotient_eq f hf Y v h) rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Produced energy continuity and higher carriers give genuine classical continuity on arbitrary parameter spaces. -/

variable {P : Type*} [TopologicalSpace P]

theorem independent_classical_fast_jet_continuous (K n : ℕ) (hn : n + 4 ≤ K)
    (c : P → ℝ → RawJet2 1 ℂ)
    (hc : ∀ Y, Tendsto (fun X => cellEnergyNorm Set.univ (c X - c Y)) (𝓝 Y) (𝓝 0))
    (u : P → TorusHk K ℂ) (t : ℝ)
    (he : ∀ Y, torusHkValueCLM (u Y) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c Y) t)
    (R : ℝ) (hb : ∀ Y, ‖u Y‖ ≤ R) (z : Vec 2) :
    Continuous (fun Y => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (u Y))) z) := by
  apply continuous_iff_continuousAt.mpr
  intro Y
  have hread (X : P) : torusHkValueCLM (u X - u Y) =ᵐ[
      volume.restrict AVenhance.unitCube] cellValue (c X - c Y) t :=
    higherCarrier_sub_raw_value_ae K _ _ _ _ t (he X) (he Y)
  have hv := carrier_value_tendsto_zero_of_raw_energy (𝓝 Y) K
    (fun X => u X - u Y) (fun X => c X - c Y) t hread (hc Y)
  exact higher_carrier_real_jet_tendsto (𝓝 Y) K n hn u (u Y) hv R
    (Filter.Eventually.of_forall hb) z

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The literal complex spatial integral equals the actual complex weak cell form. -/

/-- Spatial integration of the complex expression reads the exact generator and source forms. -/
theorem dataComplexSpatial_integral (P : MolecularData)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    (∫ x in AVenhance.unitCube, dataComplexSpatial P t u z S F x) =
      dataComplexGenerator P t u z + cellComplexSource (0 : Fin 2 → ℂ) S F z := by
  let m := fun j k x => dataMetricEntryCLM P t j k (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u) x *
    star (cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) k z x)
  let d := fun j x => cellDriftEntryCLM (dataCoefficients P) P.V P.drift_measurable P.drift_bounded t j (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u) x *
    star (torusHkValueCLM z x)
  let p := fun x => cellScalarCLM (0 : ℂ) (torusHkValueCLM u) x * star (torusHkValueCLM z x)
  let s := fun x => S x * star (torusHkValueCLM z x)
  let f := fun j x => F j x * star (cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j z x)
  have hm (j k : Fin 2) : Integrable (m j k) (volume.restrict AVenhance.unitCube) :=
    cellComplex_pairing_integrable _ _
  have hd (j : Fin 2) : Integrable (d j) (volume.restrict AVenhance.unitCube) :=
    cellComplex_pairing_integrable _ _
  have hp : Integrable p (volume.restrict AVenhance.unitCube) := cellComplex_pairing_integrable _ _
  have hpzero : (∫ x in AVenhance.unitCube, p x) = 0 := by
    calc
      _ = ∫ _ in AVenhance.unitCube, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [cellScalarCLM_ae 0 (torusHkValueCLM u)] with x hx
        simp only [p, hx, zero_mul]
      _ = 0 := integral_zero _ _
  have hs : Integrable s (volume.restrict AVenhance.unitCube) := cellComplex_pairing_integrable _ _
  have hf (j : Fin 2) : Integrable (f j) (volume.restrict AVenhance.unitCube) :=
    cellComplex_pairing_integrable _ _
  have hms (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hm j k)
  have hmss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hms j)
  have hds : Integrable (fun x => ∑ j : Fin 2, d j x) (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have hfs : Integrable (fun x => ∑ j : Fin 2, f j x) (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hf j)
  have h1 := integral_sub (((hmss.neg.sub hds).add hp).add hs) hfs
  have h2 := integral_add ((hmss.neg.sub hds).add hp) hs
  have h3 := integral_add (hmss.neg.sub hds) hp
  have h4 := integral_sub hmss.neg hds
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at h1 h2 h3 h4
  change (∫ x in AVenhance.unitCube,
    -(∑ j : Fin 2, ∑ k : Fin 2, m j k x) - (∑ j : Fin 2, d j x) + p x + s x -
      ∑ j : Fin 2, f j x) = _
  rw [h1, h2, h3, h4, integral_neg,
    integral_finsetSum Finset.univ (fun j _ => hms j),
    integral_finsetSum Finset.univ (fun j _ => hd j),
    integral_finsetSum Finset.univ (fun j _ => hf j)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hm _ k)]
  rw [hpzero]
  dsimp only [dataComplexGenerator, cellComplexSource, cellComplexPair, m, d, p, s, f]
  simp only [Pi.zero_apply, star_zero, show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl,
    cellShiftedDerivative_zero, dataCoefficients]
  ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Inherited flux reserves preserve each input component through every finite word. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedSourceFluxComponentReserve (H : ℕ) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (η : ℝ) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (Qf : ∀ u : ι, JointSourceReserve (H + D) (fun t z Y => f t z Y u))
    (Qedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      JointSourceReserve H (fun t z Y => γ.coeff α t Y z))
    (k : Fin 2) (j : ℕ) (v : ι) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceFluxComponentCoefficient edge η t
        (fun X y => Real.exp (A X) • f t y X) k j v Y z) := by
  let F := fun (u : ι) (d : Finset.Icc 2 D)
      (γ : Constituent d.val ℝ ℝ) (α : DerivativeWord2 (d.val - 1)) t z Y =>
    γ.coeff α t Y z k • γ.map
      ((Real.exp (A Y))⁻¹ • covariantListCoefficients η (List.ofFn α)
        (fun X y => Real.exp (A X) • f t y X u) j Y z)
  let Qword := fun (u : ι) (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.val - 1)) =>
    normalizedCovariantListReserve (Qf u) H A η (List.ofFn α)
      (by simp only [List.length_ofFn]; have hd := (Finset.mem_Icc.mp d.property).2; omega) j
  let Q := fun (u : ι) (d : Finset.Icc 2 D)
      (γ : Constituent d.val ℝ ℝ) (hγ : γ ∈ edge v u d)
      (α : DerivativeWord2 (d.val - 1)) =>
    ((Qedge v u d γ hγ α).map
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)).scalarProduct
        ((Qword u d α).map γ.map)
  let S := JointSourceReserve.fintypeSum H
    (fun u t z Y => ∑ d : Finset.Icc 2 D,
      ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
    (fun u => JointSourceReserve.fintypeSum H
      (fun d t z Y => ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
      (fun d => JointSourceReserve.listSum (edge v u d) H
        (fun γ t z Y => ∑ α, F u d γ α t z Y)
        (fun γ hγ => JointSourceReserve.fintypeSum H (F u d γ) (Q u d γ hγ))))
  have he : (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceFluxComponentCoefficient edge η t
        (fun X y => Real.exp (A X) • f t y X) k j v Y z) =
      fun t z Y => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum := by
    funext t z Y
    simp only [sourceFluxComponentCoefficient, Pi.smul_apply, Finset.smul_sum, List.smul_sum, List.map_map,
      Function.comp_def]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro d _
    apply congrArg List.sum
    apply List.map_congr_left
    intro γ _
    apply Finset.sum_congr rfl
    intro α _
    change (Real.exp (A Y))⁻¹ • (γ.coeff α t Y z k • γ.map _) =
      γ.coeff α t Y z k • γ.map ((Real.exp (A Y))⁻¹ • _)
    rw [map_smul]
    exact smul_comm _ _ _
  rw [he]
  exact S

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal
namespace AVRegularity.EntryWeakProofs

/-! Strongly measurable higher carriers have genuine jointly measurable classical readouts. -/

theorem realHigherCarrier_lift_continuous (K : ℕ) (hK : 2 ≤ K) (z : Vec 2) :
    Continuous (fun w : TorusHk K ℂ => realClassicalLift K (mapTorusHk Complex.reCLM w) z) := by
  let C : ℝ≥0 := ⟨cellClassicalSobolevConstant K 0, cellClassicalSobolevConstant_nonneg K 0⟩
  apply LipschitzWith.continuous (K := C)
  apply LipschitzWith.of_dist_le_mul
  intro w v
  rw [dist_eq_norm, dist_eq_norm]
  have he : realClassicalLift K (mapTorusHk Complex.reCLM w) z -
      realClassicalLift K (mapTorusHk Complex.reCLM v) z =
        realClassicalLift K (mapTorusHk Complex.reCLM (w - v)) z := by
    have hm : mapTorusHk Complex.reCLM (w - v) =
        mapTorusHk Complex.reCLM w - mapTorusHk Complex.reCLM v := by
      simpa only [mapTorusHkCLM_apply] using (mapTorusHkCLM K Complex.reCLM).map_sub w v
    rw [hm, realClassicalLift_sub K hK]
    rfl
  rw [he]
  have hCv : (C : ℝ) = cellClassicalSobolevConstant K 0 := rfl
  rw [hCv]
  simpa only [norm_iteratedFDeriv_zero] using
    realHigherCarrier_derivative_norm_le K 0 (by omega) (w - v) z

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! A higher Sobolev trace has the same literal gradient as the original weak jet. -/

theorem higherTrace_gradient_ae (K : ℕ) (w : TorusHk (K + 1) ℂ) (D : RawJet2 1 ℂ)
    (hD : HasPeriodicOrderedWeakJet D)
    (hw : torusHkValueCLM w =ᵐ[volume.restrict AVenhance.unitCube] D (valueIndex2 1)) :
    torusHkValueCLM (torusGradientTensor w) =ᵐ[volume.restrict AVenhance.unitCube]
      cellGradient D := by
  let z : TorusHk 1 ℂ := (⟨D, hD⟩ : TorusHkFunction 1 ℂ).toHk
  let w1 := truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) w
  have hv : torusHkValueCLM w1 = torusHkValueCLM z := by
    apply Lp.ext
    exact hw.trans (torusJetToL2_ae D hD.2.1 (valueIndex2 1)).symm
  have he : w1 = z := cellH1Value_injective hv
  have hc (j : Fin 2) : w.val ⟨⟨1, by omega⟩, fun _ => j⟩ =ᵐ[
      volume.restrict AVenhance.unitCube] cellGradComp D j := by
    have hh := torusJetToL2_ae D hD.2.1 (⟨⟨1, by decide⟩, fun _ => j⟩ : JetIndex2 1)
    change (z.val ⟨⟨1, by decide⟩, fun _ => j⟩ : Vec 2 → ℂ) =ᵐ[_] cellGradComp D j at hh
    rw [← he] at hh
    exact hh
  filter_upwards [torusGradientTensor_value_ae w, Filter.eventually_all.2 hc] with x hx hy
  change (torusGradientTensor w).val (valueIndex2 K) x = cellGradient D x
  rw [hx]
  apply PiLp.ext
  intro j
  exact hy j

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Agreement of the complex Hilbert form integrand with the public literal weak integrand. -/

/-- A trial class, conjugate test class, and source classes read the exact raw cell integrand. -/
theorem dataComplexSpatial_literal_ae (P : MolecularData)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (rawu : Vec 2 → ℂ) (rawdu : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (flux : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hu : (torusHkValueCLM u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawu)
    (hdu : ∀ j, (cellDerivativeCLM j u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawdu j)
    (hz : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star ψ)
    (hdz : ∀ j, (cellDerivativeCLM j z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star (dψ j))
    (hS : (S : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] src)
    (hF : ∀ j, (F j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => flux x j) :
    dataComplexSpatial P t u z S F =ᵐ[volume.restrict AVenhance.unitCube]
      cellLiteralRHS (dataCoefficients P) t rawu rawdu ψ dψ src flux := by
  have hm := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k =>
    dataMetricEntryCLM_ae P t j k (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u)))
  have hd := ae_all_iff.mpr (fun j => cellDriftEntryCLM_ae (dataCoefficients P) P.V P.drift_measurable P.drift_bounded t j (cellShiftedDerivativeCLM (0 : Fin 2 → ℂ) j u))
  have hshift := ae_all_iff.mpr (fun j => cellShiftedDerivativeCLM_ae (0 : Fin 2 → ℂ) j u)
  have htest := ae_all_iff.mpr (fun j => cellConjugateTest_shift_ae (0 : Fin 2 → ℂ) z ψ dψ hz hdz j)
  filter_upwards [hm, hd, hshift, htest, hu, hz, hS, ae_all_iff.mpr hF,
    ae_all_iff.mpr hdu, cellScalarCLM_ae (0 : ℂ) (torusHkValueCLM u)]
    with x hmx hdx hsx htx hux hzx hSx hFx hdux hpx
  have hstar : star (torusHkValueCLM z x) = ψ x := by
    rw [hzx]
    exact star_star _
  simp only [dataComplexSpatial, cellLiteralRHS, Fin.sum_univ_two,
    hmx, hdx, hsx, htx, hux, hstar, hSx, hFx, hdux, hpx]
  rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Strongly measurable higher carriers have genuine jointly measurable classical readouts. -/

theorem realHigherCarrier_lift_joint_measurable (K : ℕ) (hK : 2 ≤ K)
    (u : ℝ → TorusHk K ℂ) (hu : StronglyMeasurable u) :
    Measurable (fun X : ℝ × Vec 2 => realClassicalLift K (mapTorusHk Complex.reCLM (u X.1)) X.2) := by
  exact carrier_joint_readout_measurable
    (fun w z => realClassicalLift K (mapTorusHk Complex.reCLM w) z)
    (realHigherCarrier_lift_continuous K hK)
    (fun w => (realClassicalLift_contDiff K 0 (by omega) (mapTorusHk Complex.reCLM w)).continuous) u hu

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Genuine finite source reserves produce the actual centered higher source and quotient data. -/

variable {K : ℕ} {f : ℝ → Vec 2 → Vec 2 → ℂ}
  {F : ℝ → Vec 2 → Vec 2 → ComplexCellVector}

def JointSourceReserve.higherSourceData (Qf : JointSourceReserve K f)
    (QF : JointSourceReserve K F) (a b : ℝ) (Y : Vec 2) :
    HigherSourceCarrierData (Set.Icc a b) K
      (fun t => cellQ0 (fun z => f t z Y)) (fun t z => F t z Y) :=
  finiteMeanFreeHigherSourceData a b K (fun t z => f t z Y) (fun t z => F t z Y)
    (fun t => Qf.fast_contDiff t Y) (fun t => QF.fast_contDiff t Y)
    (fun t => Qf.periodic t Y) (fun t => QF.periodic t Y)
    (Qf.measurable Y) (QF.measurable Y) Qf.budget QF.budget Qf.budget_nonneg QF.budget_nonneg
    (fun n hn t z => Qf.fast_derivative_bound n hn t Y z)
    (fun n hn t z => QF.fast_derivative_bound n hn t Y z)

def JointSourceReserve.quotientHigherSourceData (Qf : JointSourceReserve (K + 1) f)
    (QF : JointSourceReserve (K + 1) F) (a b : ℝ) (Y v : Vec 2) (h : ℝ) (hh : h ≠ 0) :
    HigherSourceCarrierData (Set.Icc a b) K
      (h⁻¹ • ((fun t => cellQ0 (fun z => f t z (Y + h • v))) -
        (fun t => cellQ0 (fun z => f t z Y))))
      (h⁻¹ • ((fun t z => F t z (Y + h • v)) - (fun t z => F t z Y))) :=
  meanFreeQuotientHigherSourceData a b K f F Qf.slice_memLp Y v h
    (slowQuotientHigherSourceData a b K f F Qf.regular QF.regular Qf.periodic QF.periodic
      Qf.measurable QF.measurable Qf.budget QF.budget Qf.budget_nonneg QF.budget_nonneg
      Qf.derivative_bound QF.derivative_bound Y v h hh)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Centered sources preserve the mean for the molecular weak evolution. -/

theorem dataComplexGenerator_one (P : MolecularData) (hv : IsCellDrift P.v)
    (t : ℝ) (u : TorusHk 1 ℂ) : dataComplexGenerator P t u cellH1One = 0 := by
  simp only [dataComplexGenerator, cellH1One_derivative, cellH1One_value,
    cellComplexPair_zero_right, Finset.sum_const_zero, neg_zero, zero_sub]
  have hz := cellDrift_constant_pair_sum (molecularCoefficients P.G P.v) hv
    P.V P.drift_bounded t u
  rw [show (∑ j : Fin 2, cellComplexPair
    (cellDriftEntryCLM (molecularCoefficients P.G P.v) P.V P.drift_measurable
      P.drift_bounded t j (cellDerivativeCLM j u)) (cellConstantCLM 1)) = 0 from hz]
  exact neg_zero

theorem dataDualComplexPair_one (P : MolecularData) (hv : IsCellDrift P.v)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (dataDualDerivative P t u S F) cellH1One = cellMean S := by
  rw [dataDualComplexPair_actual, dataComplexGenerator_one P hv, cellComplexSource_one,
    zero_add]

theorem dataWeak_mean_increment {a b : ℝ} (P : MolecularData) (hv : IsCellDrift P.v)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => dataDualDerivative P t (slice t) (S t) (F t)))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    cellMean (u t) - cellMean (u s) = ∫ r in s..t, cellMean (S r) := by
  have he := h.complex_increment s hs t ht hst cellH1One
  rw [cellH1One_value, cellComplexPair_one, cellComplexPair_one] at he
  simp_rw [dataDualComplexPair_one P hv] at he
  exact he

theorem dataWeak_mean_conserved {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hv : IsCellDrift P.v)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => dataDualDerivative P t (slice t) (S t) (F t)))
    (hS : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (S t) = 0) :
    ∀ t ∈ Icc a b, cellMean (u t) = cellMean (u a) := by
  intro t ht
  have he := dataWeak_mean_increment P hv u slice S F h a ⟨le_rfl, hab⟩ t ht ht.1
  have hz : (∫ r in a..t, cellMean (S r)) = 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    have hr := hS.filter_mono (ae_mono (Measure.restrict_mono
      (show Ioc a t ⊆ Icc a b from fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩) le_rfl))
    calc
      _ = ∫ _ in Ioc a t, (0 : ℂ) := integral_congr_ae hr
      _ = 0 := integral_zero ℝ ℂ
  rw [hz] at he
  exact sub_eq_zero.mp he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Every reserved canonical source jet has a higher quotient budget independent of the increment. -/

abbrev NonzeroIncrement := {h : ℝ // h ≠ 0}

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Spatial form identities for the literal raw cell jet and public H¹ tests. -/

/-- A raw trial jet representing an H¹ class has the exact integrable literal weak integrand. -/
theorem dataRawSpatial_equation (P : MolecularData)
    (t : ℝ) (u : TorusHk 1 ℂ) (D : RawJet2 1 ℂ)
    (hD : ∀ a, (u.val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D a)
    (ψ : TorusHkFunction 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (src : Vec 2 → ℂ) (flux : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hS : (S : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] src)
    (hF : ∀ j, (F j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => flux x j) :
    Integrable (cellLiteralRHS (dataCoefficients P) t (D (valueIndex2 1)) (cellGradComp D)
      (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) src flux)
      (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, cellLiteralRHS (dataCoefficients P) t (D (valueIndex2 1)) (cellGradComp D)
      (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) src flux x) =
      cellDualComplexPair (dataDualDerivative P t u S F) (cellRawTest ψ) := by
  have he := dataComplexSpatial_literal_ae P t u (cellRawTest ψ) S F
    (D (valueIndex2 1)) (cellGradComp D) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) src flux (hD (valueIndex2 1))
    (fun j => hD ⟨⟨1, by decide⟩, fun _ => j⟩) (cellRawTest_value_ae ψ)
    (cellRawTest_derivative_ae ψ) hS hF
  refine ⟨(dataComplexSpatial_integrable P t u _ S F).congr he, ?_⟩
  rw [← integral_congr_ae he, dataComplexSpatial_integral, ← dataDualComplexPair_actual]

end AVRegularity.EntryWeakProofs
end
