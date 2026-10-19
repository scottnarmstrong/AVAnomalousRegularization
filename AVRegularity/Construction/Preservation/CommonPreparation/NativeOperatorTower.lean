-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.FiniteSmoothPeriodicCarrier
import AVRegularity.CycleComparison.TailConstructed.RawFluxOrderZero
public import AVRegularity.Construction.Preservation.CommonPreparation.KernelSuperposition
public import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
import AVRegularity.Construction.Preservation.CommonPreparation.NeutralChainEnvelopes
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Constant elements of the periodic Sobolev carrier `TorusHk K E` for every fibre `E`: the
value jet is the constant and every jet of positive order vanishes. Used by the constant-trace
preparation (`NativeConstantTraceStatement`).

The degenerate cases are included: order `K = 0` has only the value jet; the zero vector gives the
zero element; a one-point or empty window is irrelevant here since no time variable occurs. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The constant element of order `K` with value `e`. -/
def ConstHk (K : ℕ) (e : E) : TorusHk K E :=
  AVRegularity.CycleWords.finiteSmoothPeriodicHk K (fun _ => e) contDiff_const (fun _ _ => rfl)

/-- Every jet of the constant element is the constant at order zero and zero above. -/
theorem ConstHk_val_ae (K : ℕ) (e : E) (a : JetIndex2 K) :
    (ConstHk K e).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => if a.1.val = 0 then e else 0 := by
  have h := AVRegularity.CycleWords.finiteSmoothPeriodicHk_jet_ae K (fun _ => e)
    contDiff_const (fun _ _ => rfl) a
  rw [AVRegularity.CycleComparison.TailConstructed.orderedDerivative_const_ite a.2 e] at h
  exact h

/-- The value jet of the constant element. -/
theorem ConstHk_value_ae (K : ℕ) (e : E) :
    (ConstHk K e).val (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => e := by
  simpa [valueIndex2, valueIndex] using ConstHk_val_ae K e (valueIndex2 K)

/-- Jets of positive order of the constant element vanish in the carrier. -/
theorem ConstHk_val_pos (K : ℕ) (e : E) (a : JetIndex2 K) (ha : 0 < a.1.val) :
    (ConstHk K e).val a = 0 := by
  apply Lp.ext
  filter_upwards [ConstHk_val_ae K e a,
    Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube)] with x h1 h2
  have hn : ¬ a.1.val = 0 := by omega
  rw [h1]
  simp only [hn, ↓reduceIte]
  exact h2.symm

/-- The raw representatives of positive-order jets vanish almost everywhere on the cell. -/
theorem ConstHk_jet_pos_ae (K : ℕ) (e : E) (a : JetIndex2 K) (ha : 0 < a.1.val) :
    (ConstHk K e).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
  have h := periodicJetRepresentative_ae (ConstHk K e).val a
  rw [ConstHk_val_pos K e a ha] at h
  exact h.trans (Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube))

variable [FiniteDimensional ℝ E]

/-- An order-zero element whose value is a.e. a constant is the constant element. -/
theorem eq_constHk_of_jet {f : TorusHk 0 E} {e : E}
    (hf : f.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => e) : f = ConstHk 0 e := by
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [periodicJetRepresentative_ae f.val (valueIndex2 0), hf,
    ConstHk_value_ae 0 e] with x h1 h2 h3
  rw [← h1]
  exact h2.trans h3.symm

/-- Truncating the constant element gives the constant element. -/
theorem truncate_constHk {K L : ℕ} (hKL : K ≤ L) (e : E) :
    truncateTorusHk hKL (ConstHk L e) = ConstHk K e := by
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [ConstHk_value_ae L e, ConstHk_value_ae K e] with x h1 h2
  rw [h2]
  exact h1

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Actual order-zero native evolution supplies the leading constant one and
identifies the canonical trace with every solution. The two weights need only
their respective native kernel operators; the actual evolution is the same.

The degenerate cases are included: empty and singleton families, zero datum, smallest orders, an
edgeless seed and identity geometry. No positive-order drift
estimate or division by the initial norm is used. -/

open FullLift RetainedEnergy CoupledEnergy.Variational

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

namespace Request
/-- The full route is realized by the original kernel equation on its whole window.
The equation, rather than a norm bound or final preparation clause, certifies it. -/
def RealizedEvolutionStatement (F : Request hr D Dm bw j₀)
    {X : Type*} [AddCommGroup X] [Module ℝ X] (R : F.InsertionRoute X) : Prop :=
  ∀ f : F.Data 0,
    ∃ (W : ∀ v : CompIn F.G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Y : ∀ v u (_ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
      F.G.IsRegSolution F.P F.seedK F.freshK F.φ₀ F.hφ₀ (D.κ F.G.level)
        (streamVel (D.Φ F.G.level)) 0 F.s F.tf f (fun _ _ => 0) (fun _ _ => 0)
        (fun v t => R.trace t (R.full f) v) W Y
end Request

/-- Native homogeneous energy and uniqueness discharge the evolution-trace ingredient.
This leaves the actual construction and linearity of the route as an equation input. -/
theorem evolution_trace_of_native_operators
    (F : Request hr D Dm bw j₀) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model) (ρ : ℝ)
    (hop : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      NativeEnergyOperatorAt F.P F.seedK F.freshK F.φ₀ F.hφ₀ F.G F.s F.tf ρ
        (D.κ F.G.level) 0 (fun v => F.G.mass F.law v / w v ^ 2))
    (hφ : IsAdmissibleStream (D.Φ F.G.level)) (ht : M.tp ∈ Set.Icc F.s F.tf)
    (hreal : F.RealizedEvolutionStatement R) : F.EvolutionTraceStatement R M := by
  intro w hw f
  obtain ⟨Rw, hB, hC, hS, hπ⟩ := hop w hw
  obtain ⟨W, Y, hsol⟩ := hreal f
  have hsmall : 1 * ρ / (2 * ρ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) Rw.radius_pos)).mpr
    ring_nf
    exact le_rfl
  have hstrain : 0 * 1 * ρ ^ 2 ≤ D.κ F.G.level / 8 := by
    simp only [zero_mul]
    exact div_nonneg Rw.diffusivity_pos.le (by norm_num)
  have hjets : ∀ t ∈ Set.Icc F.s F.tf, ∀ l, 1 ≤ l → l ≤ 0 → ∀ x,
      ‖coefficientDerivativeArray
        (driftCoefficient (streamVel (D.Φ F.G.level) t)) l x‖ ≤
        0 * 1 ^ l * (l.factorial : ℝ) * (2 * ρ) ^ ((1 : ℤ) - l) := by
    intro _ _ l hl hl0
    omega
  have he := native_reg_solution_homogeneous_contraction F.P F.seedK F.freshK F.φ₀ F.hφ₀
    F.G Rw hB hC hS hφ 0 1 (2 * ρ) le_rfl le_rfl
    (mul_pos (by norm_num) Rw.radius_pos) hsmall hstrain hjets f _ W Y hsol M.tp ht
  have hdiss : 0 ≤ (5 * D.κ F.G.level / 4) * ∫ t in Set.Icc F.s M.tp,
      massGradNormSq ρ Rw.π (fun v => (W v t).val) :=
    mul_nonneg (by have := Rw.diffusivity_pos; positivity)
      (integral_nonneg fun t => massGradNormSq_nonneg _ _ Rw.hπ _)
  have hmass := (le_add_of_nonneg_right hdiss).trans he
  have hn := Real.sqrt_le_sqrt hmass
  rw [hπ] at hn
  change weightedNorm ρ (F.G.mass F.law) w (R.trace M.tp (R.full f)) ≤
    weightedNorm ρ (F.G.mass F.law) w f at hn
  rw [Buffer.weightedNorm_order_zero_radius ρ 1,
    Buffer.weightedNorm_order_zero_radius ρ 1] at hn
  refine ⟨hn, ?_⟩
  intro U' W' Y' hsol'
  have hu := native_reg_solution_unique F.P F.seedK F.freshK F.φ₀ F.hφ₀ F.G
    Rw hB hC hS hφ 0 1 (2 * ρ) le_rfl le_rfl (mul_pos (by norm_num) Rw.radius_pos)
    hsmall hstrain hjets f _ U' W W' Y Y' hsol hsol'
  funext v
  exact hu v M.tp ht

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The regularized carrier of a constant higher input has no derivatives. For a constant
`H^1` input the first-order commutation clause of the regularizer shows that the first-order
jets of the regularized carrier vanish; the vanishing of all higher jets follows.

The degenerate cases are included: `D = 2` makes the carrier an `H^1` element and only the
first-order clause is used; a zero constant gives the zero input; one component and edgeless
families, since the statement is per component and per edge label. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {D : ℕ}

/-- The first-order jets of the regularized carrier of a constant input vanish. -/
theorem lift_grad_zero
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (cv : ∀ j, h j) (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : ι) (α : Γ i j) (m : Fin 2) :
    (P.lift t ht (fun j => ConstHk 1 (cv j)) i j α).val
      ⟨⟨1, by have := P.order_ge_two; omega⟩, fun _ => m⟩ = 0 := by
  have hD := P.order_ge_two
  obtain ⟨y1, hy1v, hy1g⟩ := (P.hS i j α).2.1 t ht (ConstHk 1 (P.C i j α (cv j)))
  have hz : (P.C i j α).compLp ((ConstHk 1 (cv j)).val (valueIndex2 (0 + 1))) =
      (ConstHk 1 (P.C i j α (cv j))).val (valueIndex2 1) := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLp (P.C i j α)
      ((ConstHk 1 (cv j)).val (valueIndex2 (0 + 1))),
      ConstHk_value_ae 1 (cv j), ConstHk_value_ae 1 (P.C i j α (cv j))] with x h1 h2 h3
    rw [h1]
    change P.C i j α ((ConstHk 1 (cv j)).val (valueIndex2 1) x) = _
    rw [h2, h3]
  set Y := P.lift t ht (fun j => ConstHk 1 (cv j)) i j α with hY
  have hYv : Y.val (valueIndex2 (0 + D - 1)) =
      P.S i j α t ((ConstHk 1 (P.C i j α (cv j))).val (valueIndex2 1)) := by
    rw [hY, P.lift_value]
    simp only
    rw [hz]
  have hcut : 1 ≤ 0 + D - 1 := by omega
  have hbase : truncateJetIndex hcut (valueIndex2 1) = valueIndex2 (0 + D - 1) := by
    apply Sigma.ext
    · apply Fin.ext
      simp [truncateJetIndex, valueIndex2, valueIndex]
    · apply heq_of_eq
      funext i
      exact Fin.elim0 i
  have htr : truncateTorusHk hcut Y = y1 := by
    apply TorusHk.ext_value
    rw [truncateTorusHk_apply, hbase, hYv, hy1v]
  have hm := hy1g m
  have hzg : (ConstHk 1 (P.C i j α (cv j))).val ⟨⟨1, by omega⟩, fun _ => m⟩ = 0 :=
    ConstHk_val_pos 1 _ _ (by simp)
  rw [hzg, map_zero] at hm
  have := congrArg (fun z : TorusHk 1 (G i j α) => z.val ⟨⟨1, by omega⟩, fun _ => m⟩) htr
  simp only [truncateTorusHk_apply] at this
  rw [← hm]
  exact this

/-- All jets of positive order of the regularized carrier of a constant input vanish. -/
theorem lift_jet_zero
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (cv : ∀ j, h j) (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : ι) (α : Γ i j)
    (r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ 0 + D - 1) (w : DerivativeWord2 r) :
    (P.lift t ht (fun j => ConstHk 1 (cv j)) i j α).val
      ⟨⟨r, by omega⟩, w⟩ = 0 := by
  have hD := P.order_ge_two
  exact jet_zero_of_order_one (by omega) _
    (fun m => lift_grad_zero P cv t ht i j α m) r hr hrL w
end

/-! The constant weak solution. If the datum of the order-zero kernel evolution is a
componentwise constant, the constant path with constant higher carrier and the regularized
higher input is a weak solution: every term of the weak identity contains a derivative jet
that vanishes.

The degenerate cases are included: a zero datum gives the zero solution; an empty component family
makes every statement vacuous; `D = 2` has the single differentiated order one; the one-point window
`a = b` makes the time integrals over `Ioc a a` empty. -/

section
section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The weak identity holds when the datum is the solution and every right side term vanishes. -/
theorem coupledWeakIdentity_of_vanish (μ : Measure (Vec 2)) (ν t₀ t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hint : Integrable (fun x => inner ℝ (f x) (φ x)) μ)
    (hv : ∀ s ∈ Set.Ioc t₀ t, ∀ᵐ x ∂μ,
      (∀ k, du s k x = 0) ∧ flux s x = 0 ∧ F s x = 0 ∧ g s x = 0) :
    AVRegularity.CoupledWeakIdentity μ ν t₀ t v f f φ dφ du flux F g := by
  have hr : ∀ s ∈ Set.Ioc t₀ t, ∀ᵐ x ∂μ,
      (-(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)
        + inner ℝ (g s x) (φ x)) = 0 := by
    intro s hs
    filter_upwards [hv s hs] with x ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, h4]
  refine ⟨hint, hint, fun s hs => ?_, ?_, ?_⟩
  · exact (integrable_zero _ _ _).congr ((hr s hs).mono fun x hx => hx.symm)
  · exact (integrableOn_zero).congr_fun
      (fun s hs => (integral_eq_zero_of_ae (hr s hs)).symm) measurableSet_Ioc
  · rw [sub_self, setIntegral_congr_fun measurableSet_Ioc
      (fun s hs => integral_eq_zero_of_ae (hr s hs))]
    simp

end Generic
end

/-! The constant path is a weak solution of the order-zero kernel evolution with constant
datum, with constant higher carrier and the regularized higher input.

The degenerate cases are included: zero datum, empty families, `D = 2`, and the one-point window are
covered by the generic argument (each differentiated term contains a vanishing jet). -/

section
section Jets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The inner product of two jets of torus elements is integrable on the cell. -/
theorem integrable_jet_inner {K K' : ℕ} (f : TorusHk K E) (a : JetIndex2 K)
    (φ : TorusHk K' E) (b : JetIndex2 K') :
    Integrable (fun x => inner ℝ (f.toFunction.jet a x) (φ.toFunction.jet b x))
      (volume.restrict AVenhance.unitCube) := by
  have hf := f.toFunction.hasPeriodicWeakJet.2.1 a
  have hg := φ.toFunction.hasPeriodicWeakJet.2.1 b
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp _) (hg.toLp _)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- Raw representatives of the zero element vanish almost everywhere on the cell. -/
theorem zero_jet_ae {K : ℕ} (a : JetIndex2 K) :
    (0 : TorusHk K E).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
  have h := periodicJetRepresentative_ae (0 : TorusHk K E).val a
  exact h.trans (Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube))

end Jets

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {D : ℕ}

/-- Vanishing of the regularized carrier jets of the constant input along the flux sum. -/
theorem flux_jets_ae'
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (cv : ∀ j, h j) (s : ℝ) (hs : s ∈ Set.Icc a b) (i j : ι) (α : Γ i j) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (d : ↥(Finset.Icc 2 D))
      (word : DerivativeWord2 (d.1 - 1)),
      (P.higherInput (fun j _ => ConstHk 1 (cv j)) i j α s).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x = 0 := by
  rw [ae_all_iff]
  intro d
  rw [ae_all_iff]
  intro word
  have hd := Finset.mem_Icc.1 d.2
  have hz : (P.higherInput (fun j _ => ConstHk 1 (cv j)) i j α s).val
      ⟨⟨d.1 - 1, by omega⟩, word⟩ = 0 := by
    rw [P.higherInput_of_mem _ i j α s hs]
    exact lift_jet_zero P cv s hs i j α (d.1 - 1) (by omega) (by omega) word
  have h := periodicJetRepresentative_ae
    (P.higherInput (fun j _ => ConstHk 1 (cv j)) i j α s).val ⟨⟨d.1 - 1, by omega⟩, word⟩
  rw [hz] at h
  filter_upwards [h, Lp.coeFn_zero (G i j α) 2 (volume.restrict AVenhance.unitCube)] with x h1 h2
  exact h1.trans h2

/-- The constant path with constant higher carrier is a weak solution. -/
theorem const_weak_solution
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (v : ℝ → Vec 2 → Vec 2) (f : ∀ i, TorusHk 0 (h i)) (cv : ∀ i, h i)
    (hf : ∀ i, f i = ConstHk 0 (cv i)) :
    IsKernelWeakSolutionTorus ν a b v 0 D P.B P.C P.S f 0 0 (fun i _ => f i)
      (fun i _ => ConstHk 1 (cv i))
      (P.higherInput (fun j _ => ConstHk 1 (cv j))) := by
  refine ⟨fun i => continuousOn_const, fun i => memLp_const _, fun i => ?_, fun i => rfl,
    fun i j α => P.higherInput_memLp _ (fun i => memLp_const _) i j α,
    fun i j α => P.higherInput_value_ae _ i j α, ?_⟩
  · exact Filter.Eventually.of_forall fun s =>
      (truncate_constHk (Nat.le_succ 0) (cv i)).trans (hf i).symm
  · intro i t ht φ
    refine coupledWeakIdentity_of_vanish _ _ _ _ _ _ _ _ _ _ _ _
      (integrable_jet_inner (f i) _ φ _) ?_
    intro s hs
    have hsI : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hdu : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ m : Fin 2,
        (ConstHk 1 (cv i)).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => m⟩ x = 0 := by
      rw [ae_all_iff]
      intro m
      exact ConstHk_jet_pos_ae 1 (cv i) _ (by simp)
    have hfl : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (j : ι) (α : Γ i j)
        (d : ↥(Finset.Icc 2 D)) (word : DerivativeWord2 (d.1 - 1)),
        (P.higherInput (fun j _ => ConstHk 1 (cv j)) i j α s).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x = 0 := by
      rw [ae_all_iff]
      intro j
      rw [ae_all_iff]
      intro α
      filter_upwards [flux_jets_ae' P cv s hsI i j α] with x hx d word using hx d word
    filter_upwards [hdu, hfl, zero_jet_ae (K := 0)
      (E := PiLp 2 (fun _ : Fin 2 => h i)) (valueIndex2 0), zero_jet_ae (K := 0)
      (E := h i) (valueIndex2 0)] with x h1 h2 h3 h4
    refine ⟨h1, ?_, h3, h4⟩
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun α _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.higherInput (fun j _ => ConstHk 1 (cv j)) i j α s).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) = 0 := by
      ext word
      exact h2 j α d word
    rw [h0]
    exact map_zero _
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The original-stage operator tower for common preparation.
The highest-order operator is the only production ingredient. Its lower-order
operators use the same coefficients, inclusion, kernel, mass, widths, constants
and price. The zero-order regularizer supplies every order by the gain
lemma. The uniform production statement chooses its order and constants before
stage data or datum. The degenerate cases are included: K=0, D=2, empty and singleton families,
zero/constant data, edgeless seed, identity geometry and a point window use the same bundle;
K need not be bounded by the stage invariant's Ks. -/

open FullLift RetainedEnergy

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

abbrev PreparationKernelOperator (F : Request hr D Dm bw j₀) (n : ℕ) :=
  KernelEnergy.TorusKernelOperator (h := fun v : CompIn F.G.comps => hr v.1.root)
    (Γ := F.G.fam.Γ) (G := fun _ u _ => hr u.1.root)
    F.s F.tf (rhoStar D F.c₀ F.G.level) (D.κ F.G.level) n Dm

/-- Literal highest-order data, for both masses, with one actual regularizer. -/
structure PreparationTopOperators (F : Request hr D Dm bw j₀) (K : ℕ)
    (CK : ℕ → ℝ) (Θ : ℝ) where
  operators : ∀ (w : CompIn F.G.comps → ℝ), (w = fun _ => 1) ∨ w = F.G.marker F.law →
    PreparationKernelOperator F K
  coefficient : ∀ w hw, (operators w hw).B = fun (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) =>
    F.G.physCoeff v u γ d.1
  inclusion : ∀ w hw, (operators w hw).C = fun (v u : CompIn F.G.comps) (_ : F.G.fam.Γ v u) =>
    ContinuousLinearMap.id ℝ (hr u.1.root)
  kernel : ∀ w hw, (operators w hw).S = F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀
  mass : ∀ w hw, (operators w hw).π = fun v => F.G.mass F.law v / w v ^ 2
  width : ∀ w hw, (operators w hw).r = fun v u γ => (F.G.kernelOf F.P F.seedK F.freshK v u γ).width
  constants : ∀ w hw, (operators w hw).c = CK
  price : ∀ w hw, (operators w hw).θ = Θ
  width_positive : ∀ v u γ, 0 < (F.G.kernelOf F.P F.seedK F.freshK v u γ).width
  regularizer : ∀ v u γ, IsSpatialRegularizerTorus (rhoStar D F.c₀ F.G.level) 0 Dm F.s F.tf CK
    (F.G.kernelOf F.P F.seedK F.freshK v u γ).width (F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀ v u γ)

/-- The same literal data at every order through K, before the initial datum. -/
structure PreparationNativeTower (F : Request hr D Dm bw j₀) (K : ℕ)
    (CK : ℕ → ℝ) (Θ : ℝ) where
  operators : ∀ (w : CompIn F.G.comps → ℝ), (w = fun _ => 1) ∨ w = F.G.marker F.law →
    (j : Fin (K + 1)) → PreparationKernelOperator F j.val
  coefficient : ∀ w hw j, (operators w hw j).B = fun (v u : CompIn F.G.comps) (γ : F.G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) =>
    F.G.physCoeff v u γ d.1
  inclusion : ∀ w hw j, (operators w hw j).C = fun (v u : CompIn F.G.comps) (_ : F.G.fam.Γ v u) =>
    ContinuousLinearMap.id ℝ (hr u.1.root)
  kernel : ∀ w hw j, (operators w hw j).S = F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀
  mass : ∀ w hw j, (operators w hw j).π = fun v => F.G.mass F.law v / w v ^ 2
  width : ∀ w hw j, (operators w hw j).r = fun v u γ => (F.G.kernelOf F.P F.seedK F.freshK v u γ).width
  constants : ∀ w hw j, (operators w hw j).c = CK
  price : ∀ w hw j, (operators w hw j).θ = Θ
  width_positive : ∀ v u γ, 0 < (F.G.kernelOf F.P F.seedK F.freshK v u γ).width
  regularizer : ∀ v u γ, IsSpatialRegularizerTorus (rhoStar D F.c₀ F.G.level) 0 Dm F.s F.tf CK
    (F.G.kernelOf F.P F.seedK F.freshK v u γ).width (F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀ v u γ)

/-- Assembly of the finite tower; the all-order gain and order restriction
preserve every physical datum and the common price. -/
def preparation_native_tower_of_top (F : Request hr D Dm bw j₀) {K : ℕ}
    {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationTopOperators F K CK Θ) :
    PreparationNativeTower F K CK Θ := by
  let op := fun w hw (j : Fin (K + 1)) => kernelOperator_order_restrict (T.operators w hw)
    (Nat.le_of_lt_succ j.isLt) (fun v u γ => by
      rw [T.constants w hw, T.width w hw, T.kernel w hw]
      exact spatial_regularizer_all_orders _ _ _ _ _ _ _ (T.regularizer v u γ) j.val)
  exact {
    operators := op
    coefficient := fun w hw j => T.coefficient w hw
    inclusion := fun w hw j => T.inclusion w hw
    kernel := fun w hw j => T.kernel w hw
    mass := fun w hw j => T.mass w hw
    width := fun w hw j => T.width w hw
    constants := fun w hw j => T.constants w hw
    price := fun w hw j => T.price w hw
    width_positive := T.width_positive
    regularizer := T.regularizer }

/-- Original-stage provenance and invariant inputs, directly available from the
seed/cascade clauses. No retained successor is substituted for F.G. -/
structure PreparationNativeSource (F : Request hr D Dm bw j₀)
    (k : InvConsts) (Mnat : ℕ) (tA S θ : ℝ) where
  seed : GenStage D hr Dm bw j₀
  menu : SuccMenu
  Cw : ℝ
  cr : ℝ
  σ₀ : ℝ
  η₀ : ℝ
  N : ℕ
  p : ℕ
  parameters : F.P = succProvParams D Cw cr σ₀ η₀ N p
  cr_le_one : cr ≤ 1
  seed_empty : ∀ v : CompIn seed.comps, v.1.births = []
  seed_tags : seed.HasTags F.P
  seed_lengths : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
    (seed.fam.identity v u γ).record.length ≤ D.eps seed.level
  seed_terminal : seed.level ≤ D.term
  cascade : IsCascadeStage D F.P menu seed F.G
  product : k.Hprod = k.G0 + menu.H + 1
  radius : F.c₀ = k.c₀
  invariant : IsStageInvariant F.law F.P F.seedK F.freshK F.φ₀ F.hφ₀ Mnat k tA F.tf S θ F.G

/-- Highest-order production and full tower production have exactly the same
uniform choices, differing only in the output bundle. -/
def PreparationOperatorOutput (top : Bool) (F : Request hr D Dm bw j₀)
    (K : ℕ) (CK : ℕ → ℝ) (Θ : ℝ) : Prop :=
  if top then Nonempty (PreparationTopOperators F K CK Θ)
  else Nonempty (PreparationNativeTower F K CK Θ)

/-- A uniform top-order or full-tower statement, with order/price choices before data.
The constants CK may be chosen after the invariant constants but before the stage;
only the zero-order regularizer is consumed, so K is unrestricted by Ks. -/
def PreparationNativeStatement (top : Bool) (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
  ∀ bw : ℝ, 0 < bw → ∀ K Dm : ℕ, 2 ≤ Dm →
  ∀ CK : ℕ → ℝ, (∀ j, j + 2 ≤ Dm → 0 ≤ CK j) →
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (CI τ c₀ : ℝ), 0 < τ → 0 < c₀ → c₀ ≤ 1 → ∀ j₀ : ℕ,
  ∃ mStar : ℕ, 2 ≤ mStar ∧
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)],
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
    IsOCStreamSeq α q Λ ζ D.Φ → ∀ M : ℕ, IsOCBandChain α q Λ ζ M D.κ → D.term = M →
  ∀ (F : Request hr D Dm bw j₀), F.c₀ = c₀ → mStar ≤ F.G.level → F.G.level ≤ M →
  ∀ (k : InvConsts) (Mnat : ℕ) (tA θ : ℝ),
    PreparationNativeSource F k Mnat tA (CI * D.eps F.G.level ^ τ) θ →
    tA ≤ F.s → F.s ≤ F.tf →
    (∀ j, j + 2 ≤ Dm → k.cker j ≤ CK j) →
    PreparationOperatorOutput top F K CK (A * (CI * D.eps F.G.level ^ τ))

/-- The uniform assembly has one remaining ingredient: its highest-order producer.
All restrictions and their literal data equalities are discharged here. -/
theorem preparation_native_statement_of_top {α q : ℝ} {ζ : ℝ → ℝ}
    (htop : PreparationNativeStatement true α q ζ) :
    PreparationNativeStatement false α q ζ := by
  obtain ⟨Λ₀, hΛ₀, htop⟩ := htop
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ bw hbw K Dm hDm CK hCK => ?_⟩
  obtain ⟨A, hA, htop⟩ := htop Λ hΛ bw hbw K Dm hDm CK hCK
  refine ⟨A, hA, fun CI τ c₀ hτ hc₀ hc₀le j₀ => ?_⟩
  obtain ⟨mStar, hmStar, htop⟩ := htop CI τ c₀ hτ hc₀ hc₀le j₀
  refine ⟨mStar, hmStar, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq M hband hterm F hc hm hmM k Mnat tA θ hsrc
    hs htf hcker
  obtain ⟨T⟩ := htop hr D hDα hDq hDΛ hDζ hseq M hband hterm F hc hm hmM k Mnat tA θ hsrc
    hs htf hcker
  exact ⟨preparation_native_tower_of_top F T⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
