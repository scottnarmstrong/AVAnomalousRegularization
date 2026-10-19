-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcDelta
public import AVRegularity.Statements.Intermediate.KernelEnergy.SchurBound
public import AVRegularity.Statements.Intermediate.Families.JetSup
import AVRegularity.CycleComparison.Lift.TransverseModeFactor
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import AVRegularity.Analysis.Schur.Finite
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Abstract positive diffusivity algebra isolates the balanced drift amplitude from scale powers. -/

theorem balanced_peclet_identity (ν B a : ℝ) (hν : 0 < ν) (hB : 0 < B) :
    Real.sqrt (ν / B) * (a / ν) = a / Real.sqrt (ν * B) := by
  rw [Real.sqrt_div hν.le, Real.sqrt_mul hν.le]
  calc
    Real.sqrt ν / Real.sqrt B * (a / ν) =
        Real.sqrt ν / Real.sqrt B * (a / (Real.sqrt ν * Real.sqrt ν)) := by
      rw [Real.mul_self_sqrt hν.le]
    _ = a / (Real.sqrt ν * Real.sqrt B) := by
      field_simp [(Real.sqrt_pos.mpr hν).ne', (Real.sqrt_pos.mpr hB).ne']

theorem balanced_peclet_le (ν B a C : ℝ) (hν : 0 < ν) (hB : 0 < B)
    (hbound : a ≤ C * Real.sqrt (ν * B)) :
    Real.sqrt (ν / B) * (a / ν) ≤ C := by
  rw [balanced_peclet_identity ν B a hν hB]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (mul_pos hν hB))).mpr hbound

/-! An original certified record controls its unweighted coefficient price at every later wavelength. -/

theorem context_record_weight_bound {e R S size : ℝ} (hR : 0 < R)
    (hRe : R ≤ e) (hS : 0 ≤ S) (d : ℕ)
    (hrecord : (e / R) ^ (d - 2) * S ≤ size) : S ≤ size := by
  have hbase : 1 ≤ e / R := (one_le_div hR).mpr hRe
  have hpow : 1 ≤ (e / R) ^ (d - 2) := one_le_pow₀ hbase
  exact (le_mul_of_one_le_left hS hpow).trans hrecord

theorem context_record_weight_bound_or_quadratic {e R S size : ℝ} (d : ℕ) (hR : 0 < R)
    (hRe : 3 ≤ d → R ≤ e) (hS : 0 ≤ S)
    (hrecord : (e / R) ^ (d - 2) * S ≤ size) : S ≤ size := by
  by_cases hd : 3 ≤ d
  · exact context_record_weight_bound hR (hRe hd) hS d hrecord
  · have hz : d - 2 = 0 := by omega
    simpa only [hz, pow_zero, one_mul] using hrecord

/-! The original ambient source cap pays every smaller effective lift reserve. -/

theorem effective_lift_reserves_le (K k L H N D Ksrc : ℕ) (hKD : Ksrc ≤ D) :
    K + 4 * (H + 1) * (N + Ksrc) ^ 2 ≤ K + 4 * (H + 1) * (N + D) ^ 2 ∧
      max k (L + 2) + H * Ksrc + 2 * N + 2 * Ksrc ≤
        max k (L + 2) + H * D + 2 * N + 2 * D := by
  have hsum : N + Ksrc ≤ N + D := Nat.add_le_add_left hKD N
  have hsquare : (N + Ksrc) ^ 2 ≤ (N + D) ^ 2 := by
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul hsum hsum
  refine ⟨Nat.add_le_add_left (Nat.mul_le_mul_left (4 * (H + 1)) hsquare) K, ?_⟩
  have hH := Nat.mul_le_mul_left H hKD
  have htwo := Nat.mul_le_mul_left 2 hKD
  omega

/-! Abstract scalar cancellation for the enhanced-radius drift strain price. -/

theorem enhanced_radius_sq {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (cr : ℝ) :
    (cr * Real.sqrt (B * τ)) ^ 2 = cr ^ 2 * B * τ := by
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hB hτ)]
  ring

theorem enhanced_drift_strain_le_of_price {B τ cr a C F : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hprice : (C * F * cr ^ 2) * (a * τ) ≤ 1 / 8) :
    (C * a) * F * (cr * Real.sqrt (B * τ)) ^ 2 ≤ B / 8 := by
  rw [enhanced_radius_sq hB hτ]
  calc
    _ = B * ((C * F * cr ^ 2) * (a * τ)) := by ring
    _ ≤ B * (1 / 8) := mul_le_mul_of_nonneg_left hprice hB
    _ = B / 8 := by ring

/-! The exact fast-coefficient cancellation in the full-lift energy estimate. -/

theorem fast_dissipation_price {ν B e ρ εc : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (he : 0 < e) (hρ : 0 < ρ)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / ρ) :
    Real.sqrt ν * (εc / e) * (ρ / Real.sqrt B) = 1 := by
  rw [hc]
  calc
    _ = (Real.sqrt ν / Real.sqrt ν) * (e / e) *
        (Real.sqrt B / Real.sqrt B) * (ρ / ρ) := by ring
    _ = 1 := by
      simp only [div_self (Real.sqrt_pos.mpr hν).ne', div_self he.ne',
        div_self (Real.sqrt_pos.mpr hB).ne', div_self hρ.ne', one_mul]

/-- A positive input jet pays for one fast derivative at the native cell scale. -/
theorem positive_input_fast_price_eq {ν B e ρ εc : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (he : 0 < e) (hρ : 0 < ρ)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / ρ)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    Real.sqrt ν * (εc ^ n / e) * ρ ^ j =
      Real.sqrt B * εc ^ (n - 1) * ρ ^ (j - 1) := by
  have hb : Real.sqrt ν * (εc / e) * ρ = Real.sqrt B := by
    apply (div_eq_one_iff_eq (Real.sqrt_pos.mpr hB).ne').mp
    simpa only [mul_div_assoc] using fast_dissipation_price hν hB he hρ hc
  have hn' : n = 1 + (n - 1) := by omega
  have hj' : j = 1 + (j - 1) := by omega
  have hpn : εc ^ n = εc * εc ^ (n - 1) := by
    conv_lhs => rw [hn']
    rw [pow_add, pow_one]
  have hpj : ρ ^ j = ρ * ρ ^ (j - 1) := by
    conv_lhs => rw [hj']
    rw [pow_add, pow_one]
  rw [hpn, hpj]
  calc
    _ = (Real.sqrt ν * (εc / e) * ρ) * εc ^ (n - 1) * ρ ^ (j - 1) := by ring
    _ = _ := by rw [hb]

/-- Small positive lift powers yield a physical positive-jet dissipation price. -/
theorem positive_input_fast_price_le {ν B e ρ εc : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (he : 0 < e) (hρ : 0 < ρ)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / ρ)
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    Real.sqrt ν * (εc ^ n / e) * ρ ^ j ≤ Real.sqrt B * ρ ^ (j - 1) := by
  rw [positive_input_fast_price_eq hν hB he hρ hc hn hj]
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_one₀ hε0 hε1) (Real.sqrt_nonneg B))
    (pow_nonneg hρ.le (j - 1))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Positive identity prices majorize their filtered list of actual constituents with multiplicities intact. -/

theorem filteredList_positive_sum_le {A B : Type*} (l : List A) (g : A → Option B)
    (w : B → ℝ≥0∞) (price : A → ℝ≥0∞)
    (hprice : ∀ a b, g a = some b → w b ≤ price a) :
    ((l.filterMap g).map w).sum ≤ (l.map price).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hg : g a with
    | none =>
      simp only [List.filterMap_cons, hg, List.map_cons, List.sum_cons]
      exact ih.trans (le_add_left le_rfl)
    | some b =>
      simp only [List.filterMap_cons, hg, List.map_cons, List.sum_cons]
      exact add_le_add (hprice a b hg) ih

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Restrict a component sum to an incoming subset when every new component has zero datum. -/

section
variable {α M : Type*} [DecidableEq α] [AddCommMonoid M]

theorem finite_own_component_sum {S T : Finset α} (hST : S ⊆ T)
    (f : {c // c ∈ T} → M) (hzero : ∀ c, c.1 ∉ S → f c = 0) :
    (∑ c : {c // c ∈ T}, f c) = ∑ v : {c // c ∈ S}, f ⟨v.1, hST v.2⟩ := by
  let F : α → M := fun c => if hc : c ∈ T then f ⟨c, hc⟩ else 0
  have hT : (∑ c : {c // c ∈ T}, f c) = ∑ c ∈ T, F c := by
    rw [Finset.sum_subtype T (fun _ => Iff.rfl) F]
    apply Finset.sum_congr rfl
    intro c _
    simp only [F, dite_eq_left c.2]
  have hS : (∑ c ∈ S, F c) = ∑ v : {c // c ∈ S}, f ⟨v.1, hST v.2⟩ := by
    rw [Finset.sum_subtype S (fun _ => Iff.rfl) F]
    apply Finset.sum_congr rfl
    intro v _
    simp only [F, dite_eq_left (hST v.2)]
  rw [hT, ← hS]
  exact (Finset.sum_subset hST (fun c hcT hcS => by
    dsimp only [F]
    rw [dite_eq_left hcT]
    exact hzero ⟨c, hcT⟩ hcS)).symm
end

/-! Restrict reserved jets by an explicit linear slow or fast parameter map. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linear_parameter_regular_and_jets (f : F → G) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ∞) f) (L : E →L[ℝ] F) (A : ℕ → ℝ)
    (hb : ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ A j) :
    ContDiff ℝ (n : ℕ∞) (f ∘ L) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ A j * ‖L‖ ^ j := by
  refine ⟨hf.comp L.contDiff, ?_⟩
  intro j hj x
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  have hh : ‖(iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L)‖ ≤
      ‖iteratedFDeriv ℝ j f (L x)‖ * ‖L‖ ^ j := by
    simpa using (iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  exact hh.trans (mul_le_mul_of_nonneg_right (hb j hj (L x)) (by positivity))
end

/-! Lowering native orders spends only the recorded length-to-kernel-width ratio. -/

theorem lowered_kernel_order_price_identity (ν e E R r : ℝ)
    (hν : ν ≠ 0) (hE : E ≠ 0) (hR : R ≠ 0) (hr : r ≠ 0) (m k : ℕ) :
    (ν * e ^ (m + k)) * E⁻¹ ^ k / (ν * r ^ m) =
      (e / R) ^ (m + k) * (R / E) ^ k * (R / r) ^ m := by
  simp only [div_pow, pow_add, inv_pow]
  field_simp [hν, hE, hR, hr]

theorem nonnegative_pow_le_max_one_pow (a : ℝ) (ha : 0 ≤ a) (m n : ℕ) (hm : m ≤ n) :
    a ^ m ≤ max 1 (a ^ n) := by
  by_cases hsmall : a ≤ 1
  · exact (pow_le_one₀ ha hsmall).trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ (le_of_not_ge hsmall) hm).trans (le_max_right _ _)

theorem lowered_kernel_order_price_le_max_of_gap (ν e E R r : ℝ)
    (hν : 0 < ν) (he : 0 ≤ e) (hE : 0 < E) (hR : 0 < R) (hr : 0 < r)
    (dout din Dmax : ℕ) (hRE : dout < din → R ≤ E)
    (hdout : 2 ≤ dout) (horder : dout ≤ din) (hD : dout ≤ Dmax) :
    (ν * e ^ (din - 2)) * E⁻¹ ^ (din - dout) / (ν * r ^ (dout - 2)) ≤
      (e / R) ^ (din - 2) * max 1 ((R / r) ^ (Dmax - 2)) := by
  have hexp : dout - 2 + (din - dout) = din - 2 := by omega
  rw [← hexp, lowered_kernel_order_price_identity ν e E R r hν.ne' hE.ne' hR.ne' hr.ne']
  have hsmall : (R / E) ^ (din - dout) ≤ 1 := by
    by_cases hgap : dout < din
    · exact pow_le_one₀ (div_nonneg hR.le hE.le) ((div_le_one hE).mpr (hRE hgap))
    · have hz : din - dout = 0 := by omega
      simp only [hz, pow_zero, le_refl]
  have hpow := nonnegative_pow_le_max_one_pow (R / r) (div_nonneg hR.le hr.le)
    (dout - 2) (Dmax - 2) (by omega)
  calc
    _ ≤ (e / R) ^ (dout - 2 + (din - dout)) * 1 * (R / r) ^ (dout - 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsmall (pow_nonneg (div_nonneg he hR.le) _))
        (pow_nonneg (div_nonneg hR.le hr.le) _)
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left hpow (pow_nonneg (div_nonneg he hR.le) _)

/-! Iterating the full derivative introduces no additional multilinear norm loss. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_nested (r q : ℕ) (f : E → F) (x : E) :
    ‖iteratedFDeriv ℝ r (iteratedFDeriv ℝ q f) x‖ = ‖iteratedFDeriv ℝ (r + q) f x‖ := by
  induction r generalizing q with
  | zero => rw [norm_iteratedFDeriv_zero, Nat.zero_add]
  | succ r ih =>
    let e : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) F ≃ₗᵢ[ℝ]
        (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :=
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q + 1) => E) F
    have he : fderiv ℝ (iteratedFDeriv ℝ q f) = e ∘ iteratedFDeriv ℝ (q + 1) f := by
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [Function.comp_apply, e, LinearIsometryEquiv.apply_symm_apply]
    rw [← norm_iteratedFDeriv_fderiv (n := r), he]
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := E)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) F)
      (G := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F)
      e (iteratedFDeriv ℝ (q + 1) f) x r, ih]
    have hi : r + (q + 1) = r + 1 + q := by omega
    rw [hi]
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Parent-fiber estimates preserve the component time supremum before the mass sum. -/

variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem parent_sum_eq (p : κ → ι) (x : κ → ℝ≥0∞) :
    (∑ i, ∑ j, if p j = i then x j else 0) = ∑ j, x j := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem parent_component_sup_sum_le (p : κ → ι) (I : Set T) (C : ℝ≥0∞)
    (F : ι → T → ℝ≥0∞) (G : κ → T → ℝ≥0∞)
    (hbound : ∀ i, ∀ t ∈ I, F i t ≤ C * ∑ j, if p j = i then G j t else 0) :
    (∑ i, ⨆ t ∈ I, F i t) ≤ C * ∑ j, ⨆ t ∈ I, G j t := by
  have hi (i : ι) : (⨆ t ∈ I, F i t) ≤
      C * ∑ j, if p j = i then (⨆ t ∈ I, G j t) else 0 := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply (hbound i t ht).trans
    apply mul_le_mul' le_rfl
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : p j = i
    · simp only [hj, ↓reduceIte]
      exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
    · simp only [hj, ↓reduceIte]
      exact le_rfl
  calc
    _ ≤ ∑ i, C * ∑ j, if p j = i then (⨆ t ∈ I, G j t) else 0 :=
      Finset.sum_le_sum fun i _ => hi i
    _ = _ := by rw [← Finset.mul_sum, parent_sum_eq]

variable [MeasurableSpace T] (μ : Measure T)

theorem parent_component_integral_sum_le (p : κ → ι) (C : ℝ≥0∞)
    (F : ι → T → ℝ≥0∞) (G : κ → T → ℝ≥0∞)
    (hG : ∀ j, AEMeasurable (G j) μ)
    (hbound : ∀ i, ∀ᵐ t ∂μ, F i t ≤ C * ∑ j, if p j = i then G j t else 0) :
    (∑ i, ∫⁻ t, F i t ∂μ) ≤ C * ∑ j, ∫⁻ t, G j t ∂μ := by
  have hterm (i : ι) (j : κ) :
      AEMeasurable (fun t => if p j = i then G j t else 0) μ := by
    by_cases hj : p j = i
    · simpa only [hj, ↓reduceIte] using hG j
    · simp only [hj, ↓reduceIte]
      exact aemeasurable_const
  have hi (i : ι) : (∫⁻ t, F i t ∂μ) ≤
      C * ∑ j, if p j = i then (∫⁻ t, G j t ∂μ) else 0 := by
    calc
      _ ≤ ∫⁻ t, C * ∑ j, if p j = i then G j t else 0 ∂μ :=
        lintegral_mono_ae (hbound i)
      _ = C * ∑ j, ∫⁻ t, (if p j = i then G j t else 0) ∂μ := by
        rw [lintegral_const_mul'' C
          (Finset.aemeasurable_fun_sum _ fun j _ => hterm i j),
          lintegral_finsetSum' _ fun j _ => hterm i j]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : p j = i <;> simp only [hj, ↓reduceIte, lintegral_zero]
  calc
    _ ≤ ∑ i, C * ∑ j, if p j = i then (∫⁻ t, G j t ∂μ) else 0 :=
      Finset.sum_le_sum fun i _ => hi i
    _ = _ := by rw [← Finset.mul_sum, parent_sum_eq]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Positive row budgets turn linear norm bounds into fixed matrix energy bounds. -/

section
variable {ι : Type*} [Fintype ι]

theorem positive_row_square_le (b x : ι → ℝ) (θ : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hrow : ∑ i, b i ≤ θ) :
    (∑ i, b i * x i) ^ 2 ≤ θ * ∑ i, b i * x i ^ 2 := by
  have hcs : (∑ i, b i * x i) ^ 2 ≤
      (∑ i, b i) * ∑ i, b i * x i ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => hb i) (fun i _ => mul_nonneg (hb i) (sq_nonneg (x i)))
      (fun i _ => le_of_eq (by ring))
  exact hcs.trans (mul_le_mul_of_nonneg_right hrow
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (sq_nonneg (x i)))))

theorem positive_row_norm_square_le (b x : ι → ℝ) (θ y : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hrow : ∑ i, b i ≤ θ)
    (hy : 0 ≤ y) (hbound : y ≤ ∑ i, b i * x i) :
    y ^ 2 ≤ θ * ∑ i, b i * x i ^ 2 := by
  exact (pow_le_pow_left₀ hy hbound 2).trans (positive_row_square_le b x θ hb hrow)
end

/-! A positive auxiliary radius absorbs any fixed finite linear budget. -/

theorem radius_linear_budget (R slack M : ℝ) (hR : 0 < R) (hs : 0 < slack)
    (hM : 0 ≤ M) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ (ρ / R) * M ≤ slack := by
  have hden : 0 < M + 1 := add_pos_of_nonneg_of_pos hM zero_lt_one
  let ρ := min R (R * (slack / (M + 1)))
  have hρ : 0 < ρ := lt_min hR (mul_pos hR (div_pos hs hden))
  have hratio : ρ / R ≤ slack / (M + 1) := by
    apply (div_le_iff₀ hR).mpr
    exact (min_le_right _ _).trans_eq (mul_comm R (slack / (M + 1)))
  refine ⟨ρ, hρ, min_le_left _ _, ?_⟩
  calc
    (ρ / R) * M ≤ (slack / (M + 1)) * M := mul_le_mul_of_nonneg_right hratio hM
    _ ≤ (slack / (M + 1)) * (M + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (div_nonneg hs.le hden.le)
    _ = slack := div_mul_cancel₀ slack hden.ne'

/-! Positive derivative powers vanish at least linearly as the auxiliary radius shrinks. -/

theorem radius_power_linear_bound {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 < R)
    (hρR : ρ ≤ R) (n : ℕ) (hn : 1 ≤ n) : ρ ^ n ≤ (ρ / R) * R ^ n := by
  cases n with
  | zero => omega
  | succ n =>
    rw [pow_succ, pow_succ]
    calc
      ρ ^ n * ρ ≤ R ^ n * ρ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρR n) hρ
      _ = (ρ / R) * (R ^ n * R) := by
        field_simp [hR.ne']

/-! A single finite jet constant controls every sampled derivative at a smaller radius. -/

def sampledJetConstant (n : ℕ) (C : ℝ) (B : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (j.factorial : ℝ) * C ^ j *
    ∑ l ∈ Finset.range (j + 1), B l

theorem sampledJetConstant_nonneg (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : ℕ → ℝ) (hB : ∀ l, 0 ≤ B l) : 0 ≤ sampledJetConstant n C B := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hC _))
    (Finset.sum_nonneg fun l _ => hB l)

theorem sampled_jet_factor_le (n j : ℕ) (hj : j ≤ n)
    (C E e ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E) (he : 0 < e)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hρe : ρ ≤ e)
    (B : ℕ → ℝ) (hB : ∀ l, 0 ≤ B l) :
    (j.factorial : ℝ) * C ^ j *
        (∑ l ∈ Finset.range (j + 1), B l * (ρ * max E⁻¹ e⁻¹) ^ l) ≤
      sampledJetConstant n C B := by
  have hs : ρ * max E⁻¹ e⁻¹ ≤ 1 := by
    rw [mul_max_of_nonneg _ _ hρ]
    apply max_le
    · simpa only [div_eq_mul_inv] using (div_le_one hE).mpr hρE
    · simpa only [div_eq_mul_inv] using (div_le_one he).mpr hρe
  have hp : 0 ≤ ρ * max E⁻¹ e⁻¹ :=
    mul_nonneg hρ (le_max_of_le_left (inv_nonneg.mpr hE.le))
  calc
    _ ≤ (j.factorial : ℝ) * C ^ j * (∑ l ∈ Finset.range (j + 1), B l) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hC _))
      apply Finset.sum_le_sum
      intro l _
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hp hs) (hB l)).trans_eq (mul_one _)
    _ ≤ sampledJetConstant n C B := by
      unfold sampledJetConstant
      apply Finset.single_le_sum (f := fun k => (k.factorial : ℝ) * C ^ k *
        ∑ l ∈ Finset.range (k + 1), B l) (a := j)
      · intro k _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hC _))
          (Finset.sum_nonneg fun l _ => hB l)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)

/-! An elementary upper bound for the actual scale exponent. -/

theorem ocDelta_lt_one {α q : ℝ} (hα : 0 ≤ α) (hq : 1 < q) : ocDelta α q < 1 := by
  have hq1 : 0 < q + 1 := by linarith only [hq]
  have hd : 0 < 8 * (q + 1) := mul_pos (by norm_num) hq1
  have hp : 0 ≤ (q - 1) / (8 * (q + 1)) := div_nonneg (by linarith only [hq]) hd.le
  have htail : 1 - (2 * q + 1) * α ≤ 1 :=
    sub_le_self _ (mul_nonneg (by linarith only [hq]) hα)
  have hident : ocDelta α q = ((q - 1) / (8 * (q + 1))) * (1 - (2 * q + 1) * α) := by
    unfold ocDelta
    have hd2 : 2 * q + 2 ≠ 0 := by linarith only [hq]
    field_simp [hq1.ne', hd2]
    ring
  rw [hident]
  apply (mul_le_mul_of_nonneg_left htail hp).trans_lt
  rw [mul_one]
  apply (div_lt_one hd).mpr
  linarith only [hq]

/-! Scalar wavelength and strain prices place the enhanced radius below the parent molecular radius. -/

theorem enhanced_radius_le_molecular_of_prices {B τ a E cr c₀ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (ha : 0 < a) (hc₀ : 0 < c₀)
    (hE : (cr / c₀) * Real.sqrt (B * τ) ≤ E)
    (hprice : (cr / c₀) ^ 2 * (a * τ) ≤ 1) :
    cr * Real.sqrt (B * τ) ≤ c₀ * min E (Real.sqrt (B / a)) := by
  have hsq : ((cr / c₀) * Real.sqrt (B * τ)) ^ 2 ≤ B / a := by
    apply (le_div_iff₀ ha).mpr
    rw [enhanced_radius_sq hB hτ]
    calc
      (cr / c₀) ^ 2 * B * τ * a = B * ((cr / c₀) ^ 2 * (a * τ)) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hprice hB
      _ = B := mul_one B
  have hh := le_min hE (Real.le_sqrt_of_sq_le hsq)
  have hm := mul_le_mul_of_nonneg_left hh hc₀.le
  simpa only [← mul_assoc, mul_div_cancel₀ _ hc₀.ne'] using hm

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Every finite real matrix has one positive row and column budget. -/

theorem finite_matrix_schur_budget {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ SchurBound M A := by
  classical
  let T : ℝ := ∑ i, ∑ j, |A i j|
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrow (i : ι) : (∑ j, A i j) ≤ T :=
    (Finset.sum_le_sum fun j _ => le_abs_self (A i j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (A k j))
        (Finset.mem_univ i))
  have hcol (j : ι) : (∑ i, A i j) ≤ T := by
    have hh : (∑ i, A i j) ≤ ∑ k, ∑ i, |A i k| := (Finset.sum_le_sum fun i _ => le_abs_self (A i j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg (A i k))
        (Finset.mem_univ j))
    rw [Finset.sum_comm] at hh
    exact hh
  refine ⟨1 + T, le_add_of_nonneg_right hT, ?_, ?_⟩
  · intro i
    exact (hrow i).trans (le_add_of_nonneg_left (by norm_num))
  · intro j
    exact (hcol j).trans (le_add_of_nonneg_left (by norm_num))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Full jets of a finite vector are bounded by the sum of their scalar component jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_vector_le_sum (d n : ℕ) (f : E → Vec d)
    (hf : ∀ c, ContDiff ℝ (n : ℕ∞) (fun X => f X c)) (X : E) :
    ‖iteratedFDeriv ℝ n f X‖ ≤ ∑ c : Fin d,
      ‖iteratedFDeriv ℝ n (fun Y => f Y c) X‖ := by
  let L (c : Fin d) : ℝ →L[ℝ] Vec d :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (Pi.single c 1)
  have hL (c : Fin d) : ‖L c‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
    intro j
    by_cases hj : j = c
    · simp [L, hj]
    · simp [L, hj]
  have he : f = fun Y => ∑ c : Fin d, L c (f Y c) := by
    funext Y c
    simp [L, Pi.single_apply]
  have hs : iteratedFDeriv ℝ n f X = ∑ c : Fin d,
      iteratedFDeriv ℝ n (fun Y => L c (f Y c)) X := by
    conv_lhs => rw [he]
    exact iteratedFDeriv_fun_sum_apply (fun c _ =>
      ((L c).contDiff.comp (hf c)).contDiffAt)
  rw [hs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  have hn := (L c).norm_iteratedFDeriv_comp_left (n := n) (x := X)
    (hf c).contDiffAt (by simp)
  exact hn.trans ((mul_le_mul_of_nonneg_right (hL c) (norm_nonneg _)).trans_eq (one_mul _))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Real component square bounds become bounds for the extended-valued strong energy. -/

theorem inverse_mass_real_bridge {π : ℝ} (hπ : 0 < π) (x : ℝ) :
    ENNReal.ofReal (π⁻¹ * x) = (ENNReal.ofReal π)⁻¹ * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hπ.le), ENNReal.ofReal_inv_of_pos hπ]

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι]

theorem inverse_mass_parent_bound (p : κ → ι) (i : ι) (C π x : ℝ)
    (σ y : κ → ℝ) (hC : 0 ≤ C) (hπ : 0 < π) (hσ : ∀ j, 0 < σ j)
    (hy : ∀ j, 0 ≤ y j)
    (hbound : π⁻¹ * x ≤ C * ∑ j, if p j = i then (σ j)⁻¹ * y j else 0) :
    (ENNReal.ofReal π)⁻¹ * ENNReal.ofReal x ≤
      ENNReal.ofReal C * ∑ j, if p j = i then
        (ENNReal.ofReal (σ j))⁻¹ * ENNReal.ofReal (y j) else 0 := by
  have hn (j : κ) : 0 ≤ (if p j = i then (σ j)⁻¹ * y j else 0) := by
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr (hσ j).le) (hy j)
    · exact le_rfl
  calc
    _ = ENNReal.ofReal (π⁻¹ * x) := (inverse_mass_real_bridge hπ x).symm
    _ ≤ ENNReal.ofReal (C * ∑ j, if p j = i then (σ j)⁻¹ * y j else 0) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = _ := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      split_ifs
      · exact inverse_mass_real_bridge (hσ j) (y j)
      · exact ENNReal.ofReal_zero

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Pointwise mixed bounds give the literal uniform-time jet supremum after the molecular clock. -/

theorem jetSup_clock_scaled_le (S T : Set ℝ) (c lam B : ℝ) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) (hclock : ∀ t ∈ S, c * t ∈ T)
    (hbound : ∀ t ∈ T, ∀ X z : Vec 2,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
        (fun w => f t (lam • Y) w) z) X‖ ≤ B) :
    jetSup S r q (fun t X z => f (c * t) (lam • X) z) ≤ ENNReal.ofReal B := by
  simp only [jetSup, ← ofReal_norm]
  exact iSup_le fun t => iSup_le fun ht => iSup_le fun X => iSup_le fun z =>
    ENNReal.ofReal_le_ofReal (hbound (c * t) (hclock t ht) X z)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Combine the componentwise parent bounds into the exact strong-energy sum and square root. -/

variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [MeasurableSpace T]

theorem parent_component_energy_sum_le (μ : Measure T) (p : κ → ι) (I : Set T)
    (C ν : ℝ≥0∞) (F W : ι → T → ℝ≥0∞) (G V : κ → T → ℝ≥0∞)
    (hV : ∀ j, AEMeasurable (V j) μ)
    (hvalue : ∀ i, ∀ t ∈ I, F i t ≤ C * ∑ j, if p j = i then G j t else 0)
    (hgrad : ∀ i, ∀ᵐ t ∂μ, W i t ≤ C * ∑ j, if p j = i then V j t else 0) :
    (∑ i, ((⨆ t ∈ I, F i t) + ν * (∫⁻ t, W i t ∂μ))) ≤
      C * (∑ j, ((⨆ t ∈ I, G j t) + ν * (∫⁻ t, V j t ∂μ))) := by
  have ha := parent_component_sup_sum_le p I C F G hvalue
  have hb := parent_component_integral_sum_le μ p C W V hV hgrad
  calc
    _ = (∑ i, ⨆ t ∈ I, F i t) + ν * ∑ i, ∫⁻ t, W i t ∂μ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ C * (∑ j, ⨆ t ∈ I, G j t) + ν * (C * ∑ j, ∫⁻ t, V j t ∂μ) :=
      add_le_add ha (mul_le_mul' le_rfl hb)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, mul_left_comm ν C]

theorem parent_component_strong_energy_le (μ : Measure T) (p : κ → ι) (I : Set T)
    (C ν : ℝ≥0∞) (F W : ι → T → ℝ≥0∞) (G V : κ → T → ℝ≥0∞)
    (hV : ∀ j, AEMeasurable (V j) μ)
    (hvalue : ∀ i, ∀ t ∈ I, F i t ≤ C * ∑ j, if p j = i then G j t else 0)
    (hgrad : ∀ i, ∀ᵐ t ∂μ, W i t ≤ C * ∑ j, if p j = i then V j t else 0) :
    (∑ i, ((⨆ t ∈ I, F i t) + ν * (∫⁻ t, W i t ∂μ))) ^ (1 / 2 : ℝ) ≤
      C ^ (1 / 2 : ℝ) *
        (∑ j, ((⨆ t ∈ I, G j t) + ν * (∫⁻ t, V j t ∂μ))) ^ (1 / 2 : ℝ) := by
  have hs := ENNReal.rpow_le_rpow
    (parent_component_energy_sum_le μ p I C ν F W G V hV hvalue hgrad) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Sum the original context ledger over native orders without counting identities or components. -/

theorem positive_context_ledger_budget (e R size : ℝ) (hsize : 0 ≤ size)
    (dout Dγ : ℕ) (hdout : 2 ≤ dout)
    (θ : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hledger : ∀ d, 2 ≤ d → d ≤ Dγ →
      (e / R) ^ (d - 2) * ∑ I, θ d I ≤ size) :
    (∑ d ∈ Finset.Icc dout Dγ, ∑ I : DerivativeWord2 (d - 1),
      θ d I * (e / R) ^ (d - 2)) ≤ (Dγ : ℝ) * size := by
  have hcard : (Finset.Icc dout Dγ).card ≤ Dγ := by
    simp only [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _d ∈ Finset.Icc dout Dγ, size := by
      apply Finset.sum_le_sum
      intro d hd
      have hh := hledger d (hdout.trans (Finset.mem_Icc.mp hd).1) (Finset.mem_Icc.mp hd).2
      simpa only [Finset.mul_sum, mul_comm] using hh
    _ = ((Finset.Icc dout Dγ).card : ℝ) * size := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hsize

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native fast dissipation cancellation over a positive physical jet density. -/

theorem positive_jet_density_fast_price_le {ν B e ρ εc : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (he : 0 < e) (hρ : 0 < ρ)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / ρ)
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (U : ℕ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    Real.sqrt ν * (εc ^ n / e) *
        (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else ρ ^ j * a j) ≤
      Real.sqrt B *
        ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else ρ ^ (j - 1) * a j := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = 0
  · simp only [ite_eq_left hj, mul_zero, le_refl]
  · simp only [ite_eq_right hj]
    rw [← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (positive_input_fast_price_le hν hB he hρ hc hε0 hε1 hn
        (Nat.one_le_iff_ne_zero.mpr hj)) (ha j)

theorem matrix_positive_jet_density_fast_price_le {ι : Type*} [Fintype ι]
    {ν B e ρ εc : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (he : 0 < e) (hρ : 0 < ρ)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / ρ)
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (U : ℕ) (M : ι → ℝ) (hM : ∀ u, 0 ≤ M u)
    (a : ι → ℕ → ℝ) (ha : ∀ u j, 0 ≤ a u j) :
    Real.sqrt ν * (εc ^ n / e) *
        (∑ u, M u * ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else ρ ^ j * a u j) ≤
      Real.sqrt B *
        ∑ u, M u * ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else ρ ^ (j - 1) * a u j := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [mul_left_comm (Real.sqrt ν * (εc ^ n / e)), mul_left_comm (Real.sqrt B)]
  exact mul_le_mul_of_nonneg_left
    (positive_jet_density_fast_price_le hν hB he hρ hc hε0 hε1 hn U (a u) (ha u)) (hM u)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Fixed positive matrix bounds preserve separate component suprema before their sum. -/

variable {ι κ T : Type*} [Fintype ι] [Fintype κ]

theorem matrix_component_sup_sum_le (A : ι → κ → ℝ≥0∞) (C : ℝ≥0∞)
    (hcol : ∀ j, ∑ i, A i j ≤ C) (I : Set T)
    (F : ι → T → ℝ≥0∞) (G : κ → T → ℝ≥0∞)
    (hbound : ∀ i, ∀ t ∈ I, F i t ≤ ∑ j, A i j * G j t) :
    (∑ i, ⨆ t ∈ I, F i t) ≤ C * ∑ j, ⨆ t ∈ I, G j t := by
  have hi (i : ι) : (⨆ t ∈ I, F i t) ≤ ∑ j, A i j * (⨆ t ∈ I, G j t) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact (hbound i t ht).trans (Finset.sum_le_sum (fun j _ =>
      mul_le_mul' le_rfl (le_iSup_of_le t (le_iSup_of_le ht le_rfl))))
  calc
    _ ≤ ∑ i, ∑ j, A i j * (⨆ t ∈ I, G j t) := Finset.sum_le_sum (fun i _ => hi i)
    _ = ∑ j, (∑ i, A i j) * (⨆ t ∈ I, G j t) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ j, C * (⨆ t ∈ I, G j t) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul' (hcol j) le_rfl)
    _ = _ := (Finset.mul_sum _ _ _).symm

variable [MeasurableSpace T]

theorem matrix_component_integral_sum_le (μ : Measure T)
    (A : ι → κ → ℝ≥0∞) (C : ℝ≥0∞) (hcol : ∀ j, ∑ i, A i j ≤ C)
    (F : ι → T → ℝ≥0∞) (G : κ → T → ℝ≥0∞)
    (hG : ∀ j, AEMeasurable (G j) μ)
    (hbound : ∀ i, ∀ᵐ t ∂μ, F i t ≤ ∑ j, A i j * G j t) :
    (∑ i, ∫⁻ t, F i t ∂μ) ≤ C * ∑ j, ∫⁻ t, G j t ∂μ := by
  have hi (i : ι) : (∫⁻ t, F i t ∂μ) ≤ ∑ j, A i j * ∫⁻ t, G j t ∂μ := by
    apply (lintegral_mono_ae (hbound i)).trans_eq
    rw [lintegral_finsetSum' Finset.univ
      (f := fun j t => A i j * G j t) (fun j _ => aemeasurable_const.mul (hG j))]
    apply Finset.sum_congr rfl
    intro j _
    exact lintegral_const_mul'' (A i j) (hG j)
  calc
    _ ≤ ∑ i, ∑ j, A i j * ∫⁻ t, G j t ∂μ := Finset.sum_le_sum (fun i _ => hi i)
    _ = ∑ j, (∑ i, A i j) * ∫⁻ t, G j t ∂μ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ j, C * ∫⁻ t, G j t ∂μ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul' (hcol j) le_rfl)
    _ = _ := (Finset.mul_sum _ _ _).symm

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Absorb an entrywise linear perturbation using its row and column budgets. -/

theorem schur_slope_budget {ι : Type*} [Fintype ι]
    (A B C : ι → ι → ℝ) (θ₀ θ M r : ℝ) (hr : 0 ≤ r)
    (hA : SchurBound θ₀ A) (hC : SchurBound M C)
    (hB : ∀ i j, B i j ≤ A i j + r * C i j)
    (hprice : θ₀ + r * M ≤ θ) : SchurBound θ B := by
  constructor
  · intro i
    calc
      (∑ j, B i j) ≤ ∑ j, (A i j + r * C i j) := Finset.sum_le_sum fun j _ => hB i j
      _ = (∑ j, A i j) + r * ∑ j, C i j := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ θ₀ + r * M := add_le_add (hA.1 i) (mul_le_mul_of_nonneg_left (hC.1 i) hr)
      _ ≤ θ := hprice
  · intro j
    calc
      (∑ i, B i j) ≤ ∑ i, (A i j + r * C i j) := Finset.sum_le_sum fun i _ => hB i j
      _ = (∑ i, A i j) + r * ∑ i, C i j := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ θ₀ + r * M := add_le_add (hA.2 j) (mul_le_mul_of_nonneg_left (hC.2 j) hr)
      _ ≤ θ := hprice

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Copy-adapt the compiled finite coordinate synthesis to the joint slow-fast parameter dimension. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem finite_fderiv_parameter_stronglyMeasurable {d : ℕ} (f : T → Vec d → E)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t))
    (x : Vec d) : StronglyMeasurable (fun t => fderiv ℝ (f t) x) := by
  have hvec (ξ : Vec d) : ξ = ∑ q : Fin d, ξ q • basisVec q := by
    funext j
    simp [basisVec, Pi.single_apply]
  let S := fun v : Fin d → E => ∑ q : Fin d,
    (ContinuousLinearMap.proj q : Vec d →L[ℝ] ℝ).smulRight (v q)
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro q _
    exact (ContinuousLinearMap.smulRightL ℝ (Vec d) E
      (ContinuousLinearMap.proj q)).continuous.comp (continuous_apply q)
  have hv : StronglyMeasurable (fun t (q : Fin d) => fderiv ℝ (f t) x (basisVec q)) :=
    (measurable_pi_iff.mpr (fun q => CycleComparison.Lift.fderiv_apply_parameter_measurable f hm hd x (basisVec q))).stronglyMeasurable
  have he : (fun t => fderiv ℝ (f t) x) =
      fun t => S (fun q => fderiv ℝ (f t) x (basisVec q)) := by
    funext t
    apply ContinuousLinearMap.ext
    intro ξ
    conv_lhs => rw [hvec ξ]
    simp [S, map_smul, ContinuousLinearMap.smulRight_apply]
  rw [he]
  simpa only [Function.comp_def] using! hS.comp_stronglyMeasurable hv

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Reuse the finite Schur bilinear theorem for vectors of component trajectory amplitudes. -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem finiteSchur_amplitudes (b : ι → κ → ℝ) (y : κ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ i j, 0 ≤ b i j)
    (hrow : ∀ i, ∑ j, b i j ≤ C) (hcol : ∀ j, ∑ i, b i j ≤ C) :
    Real.sqrt (∑ i, (∑ j, b i j * y j) ^ 2) ≤ C * Real.sqrt (∑ j, y j ^ 2) := by
  let x := fun i => ∑ j, b i j * y j
  have hs := Analysis.Schur.finiteSchurBilinear Finset.univ Finset.univ b x y C hC
    (fun i _ j _ => hb i j) (fun i _ => hrow i) (fun j _ => hcol j)
  have he : (∑ i, ∑ j, b i j * x i * y j) = ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = x i * ∑ j, b i j * y j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = x i ^ 2 := by change x i * x i = x i ^ 2; ring
  rw [he] at hs
  have hX : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hz : Real.sqrt (∑ i, x i ^ 2) = 0
  · rw [hz]
    exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have hp : 0 < Real.sqrt (∑ i, x i ^ 2) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    have hh : Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) ≤
        Real.sqrt (∑ i, x i ^ 2) * (C * Real.sqrt (∑ j, y j ^ 2)) := by
      rw [Real.mul_self_sqrt hX]
      exact hs.trans_eq (by ring)
    exact le_of_mul_le_mul_left hh hp

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Restrict full joint jets to independent slow and fast increments with their exact scale powers. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mixed_linear_parameter_jet_norm_le (r q : ℕ) (f : E → F)
    (hf : ContDiff ℝ (r + q : ℕ∞) f) (Lslow Lfast : Vec 2 →L[ℝ] E) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (fun w => f (Lslow Y + Lfast w)) z) X‖ ≤
      ‖iteratedFDeriv ℝ (r + q) f (Lslow X + Lfast z)‖ * ‖Lslow‖ ^ r * ‖Lfast‖ ^ q := by
  let R := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
    (E := fun _ : Fin q => Vec 2) (E₁ := fun _ : Fin q => E) (F := F) (fun _ => Lfast)
  let J := iteratedFDeriv ℝ q f
  let g : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F :=
    fun Y => J (Lslow Y + Lfast z)
  have hJ : ContDiff ℝ (r : ℕ∞) J := hf.iteratedFDeriv_right (by norm_cast)
  have hg : ContDiff ℝ (r : ℕ∞) g := hJ.comp (Lslow.contDiff.add contDiff_const)
  have he : (fun Y => iteratedFDeriv ℝ q (fun w => f (Lslow Y + Lfast w)) z) = R ∘ g := by
    funext Y
    have htrans : ContDiff ℝ (r + q : ℕ∞) (fun y : E => f (Lslow Y + y)) :=
      hf.comp (contDiff_const.add contDiff_id)
    change iteratedFDeriv ℝ q ((fun y : E => f (Lslow Y + y)) ∘ Lfast) z = _
    rw [Lfast.iteratedFDeriv_comp_right htrans z (by norm_cast; omega),
      iteratedFDeriv_comp_add_left]
    rfl
  have hR : ‖R‖ ≤ ‖Lfast‖ ^ q := by
    simpa [R] using ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      F (fun _ : Fin q => Lfast)
  have hgn : ‖iteratedFDeriv ℝ r g X‖ ≤
      ‖iteratedFDeriv ℝ (r + q) f (Lslow X + Lfast z)‖ * ‖Lslow‖ ^ r := by
    change ‖iteratedFDeriv ℝ r ((fun y : E => J (y + Lfast z)) ∘ Lslow) X‖ ≤ _
    have htrans : ContDiff ℝ (r : ℕ∞) (fun y : E => J (y + Lfast z)) :=
      hJ.comp (contDiff_id.add contDiff_const)
    rw [Lslow.iteratedFDeriv_comp_right htrans X (by simp),
      iteratedFDeriv_comp_add_right]
    have hh : ‖(iteratedFDeriv ℝ r J (Lslow X + Lfast z)).compContinuousLinearMap
        (fun _ => Lslow)‖ ≤ ‖iteratedFDeriv ℝ r J (Lslow X + Lfast z)‖ * ‖Lslow‖ ^ r := by
      simpa using (iteratedFDeriv ℝ r J (Lslow X + Lfast z)).norm_compContinuousLinearMap_le
        (fun _ => Lslow)
    simpa only [J, norm_iteratedFDeriv_nested] using hh
  rw [he]
  have hn := R.norm_iteratedFDeriv_comp_left (n := r) (x := X) hg.contDiffAt (by simp)
  exact hn.trans ((mul_le_mul hR hgn (norm_nonneg _) (by positivity)).trans_eq (by ring))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Collapse the finite Piola sums against each identity's original weighted record. -/

theorem positive_transport_record_budget (e R A C Cs mapNorm size : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCs : 0 ≤ Cs) (hmap : 0 ≤ mapNorm) (hsize : 0 ≤ size)
    (dout Dγ Dmax : ℕ) (hdout : 2 ≤ dout) (hout : dout ≤ Dmax)
    (θ : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hledger : ∀ d, 2 ≤ d → d ≤ Dγ →
      (e / R) ^ (d - 2) * ∑ I, θ d I ≤ size) :
    (∑ _a : Fin 2, ∑ _W : DerivativeWord2 (dout - 1), mapNorm *
      (∑ d ∈ Finset.Icc dout Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        C * Cs * (θ d I * (e / R) ^ (d - 2) * A))) ≤
      4 * (2 : ℝ) ^ Dmax * mapNorm * C * Cs * A * (Dγ : ℝ) * size := by
  have hfac : 0 ≤ 2 * C * Cs * A := by positivity
  have heq d : (∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      C * Cs * (θ d I * (e / R) ^ (d - 2) * A)) =
        (2 * C * Cs * A) * (∑ I : DerivativeWord2 (d - 1), θ d I * (e / R) ^ (d - 2)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  have hb : (∑ d ∈ Finset.Icc dout Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      C * Cs * (θ d I * (e / R) ^ (d - 2) * A)) ≤
        (2 * C * Cs * A) * ((Dγ : ℝ) * size) := by
    simp_rw [heq]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (positive_context_ledger_budget e R size hsize dout Dγ hdout θ hledger) hfac
  have hcard : (Fintype.card (DerivativeWord2 (dout - 1)) : ℝ) ≤ (2 : ℝ) ^ Dmax := by
    have he : Fintype.card (DerivativeWord2 (dout - 1)) = 2 ^ (dout - 1) := by
      simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin]
    rw [he, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) ((Nat.sub_le dout 1).trans hout)
  calc
    _ ≤ ∑ _a : Fin 2, ∑ _W : DerivativeWord2 (dout - 1),
        mapNorm * ((2 * C * Cs * A) * ((Dγ : ℝ) * size)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro W _
      exact mul_le_mul_of_nonneg_left hb hmap
    _ = 2 * (Fintype.card (DerivativeWord2 (dout - 1)) : ℝ) *
        (mapNorm * ((2 * C * Cs * A) * ((Dγ : ℝ) * size))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ 2 * (2 : ℝ) ^ Dmax *
        (mapNorm * ((2 * C * Cs * A) * ((Dγ : ℝ) * size))) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num))
      positivity
    _ = _ := by ring

/-! Finite coordinate synthesis commutes with ordered classical derivatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_finite_sum {ι : Type*} [Fintype ι] {m : ℕ}
    (w : DerivativeWord2 m) (f : ι → Vec 2 → E)
    (hf : ∀ i, ContDiff ℝ (m : ℕ∞) (f i)) :
    orderedDerivative w (fun x => ∑ i, f i x) = fun x => ∑ i, orderedDerivative w (f i) x := by
  have hsum : ContDiff ℝ (m : ℕ∞) (fun x => ∑ i, f i x) := ContDiff.sum fun i _ => hf i
  rw [orderedDerivative_eq_iteratedFDeriv w hsum]
  funext x
  have hi := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (u := Finset.univ) (f := f)
    (i := m) (fun i _ => hf i)) x
  simp only [Finset.sum_apply] at hi
  rw [hi]
  simp only [sum_apply]
  exact Finset.sum_congr rfl fun i _ => congrFun
    (orderedDerivative_eq_iteratedFDeriv w (hf i)).symm x

theorem orderedDerivative_coordinate_synthesis {ι : Type*} [Fintype ι] {m : ℕ}
    (w : DerivativeWord2 m) (a : ι → Vec 2 → ℝ) (e : ι → E)
    (ha : ∀ i, ContDiff ℝ (m : ℕ∞) (a i)) :
    orderedDerivative w (fun x => ∑ i, a i x • e i) =
      fun x => ∑ i, orderedDerivative w (a i) x • e i := by
  have hterm (i : ι) : ContDiff ℝ (m : ℕ∞) (fun x => a i x • e i) :=
    (ha i).smul contDiff_const
  rw [orderedDerivative_finite_sum w _ hterm]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (orderedDerivative_clm_comp (ContinuousLinearMap.smulRight
    (ContinuousLinearMap.id ℝ ℝ) (e i)) w (ha i)) x
end

end AVRegularity.Construction.Preservation.FullLift
end
end
