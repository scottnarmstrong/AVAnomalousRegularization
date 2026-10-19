-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.HigherCarrierSum
import AVRegularity.CycleEvolution.CellDriftComplexMultiplier
public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleJoint.PlaneH1TimeMemLpReadouts
public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Covariant words retain a single stored amplitude with an explicit finite direction constant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem covariant_scalar_map_norm_le (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) :
    ‖A (basisVec i) • ContinuousLinearMap.id ℝ E‖ ≤ ‖A‖ := by
  have hA : ‖A (basisVec i)‖ ≤ ‖A‖ := by
    simpa only [ChartTransport.norm_basisVec, mul_one] using A.le_opNorm (basisVec i)
  calc
    _ = ‖A (basisVec i)‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul _ _
    _ ≤ ‖A‖ * 1 := mul_le_mul hA ContinuousLinearMap.norm_id_le (norm_nonneg _) (norm_nonneg A)
    _ = _ := mul_one _

theorem JointSourceReserve.covariantWord_budget_le {H : ℕ}
    {f : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f)
    (θ B : ℝ) (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (n R : ℕ) (hNR : n + R ≤ H) (A : Vec 2 →L[ℝ] ℝ)
    (α : DerivativeWord2 n) (r : ℕ) (hr : r ≤ R) :
    (Q.covariantWord n R hNR A α).budget r ≤ (1 + ‖A‖) ^ n * (θ * B) := by
  induction n generalizing R r with
  | zero =>
      change Q.budget r ≤ (1 + ‖A‖) ^ 0 * (θ * B)
      rw [pow_zero, one_mul]
      exact hQ r (by omega)
  | succ n ih =>
      let P := Q.covariantWord n (R + 1) (by omega) A (fun i => α i.castSucc)
      change (P.covariantSlow R (by omega) A (α (Fin.last n))).budget r ≤ _
      rw [JointSourceReserve.covariantSlow_budget]
      have h1 : P.budget (1 + r) ≤ (1 + ‖A‖) ^ n * (θ * B) :=
        ih (R + 1) (by omega) (fun i => α i.castSucc) (1 + r) (by omega)
      have h0 : P.budget r ≤ (1 + ‖A‖) ^ n * (θ * B) :=
        ih (R + 1) (by omega) (fun i => α i.castSucc) r (by omega)
      have hm := mul_le_mul (covariant_scalar_map_norm_le (E := E) A (α (Fin.last n))) h0
        (P.budget_nonneg r) (norm_nonneg A)
      apply (add_le_add h1 hm).trans_eq
      rw [pow_succ]
      ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Measurability and finite time bounds for the actual higher metric-gradient carrier. -/

theorem metricGradientCarrier_stronglyMeasurable {A : Type*} [MeasurableSpace A]
    (K : ℕ) (G : A → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, Measurable (fun a => G a i j))
    (w : A → TorusHk (K + 1) ℂ) (hw : StronglyMeasurable w) :
    StronglyMeasurable (fun a => metricGradientCarrier K (G a) (w a)) := by
  have ht (i j : Fin 2) : StronglyMeasurable
      (fun a => G a i j • metricEntryGradientCLM K i j (w a)) :=
    (hG i j).stronglyMeasurable.smul
      ((metricEntryGradientCLM K i j).continuous.comp_stronglyMeasurable hw)
  have hi (i : Fin 2) : StronglyMeasurable
      (fun a => ∑ j : Fin 2, G a i j • metricEntryGradientCLM K i j (w a)) := by
    simpa only [Finset.sum_fn] using Finset.stronglyMeasurable_sum Finset.univ
      (fun j _ => ht i j)
  simpa only [metricGradientCarrier, Finset.sum_fn] using
    Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hi i)

theorem metricGradientCarrier_memLp {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ]
    (K : ℕ) (G : A → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, Measurable (fun a => G a i j))
    (w : A → TorusHk (K + 1) ℂ) (hw : StronglyMeasurable w)
    (B R : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a i j, |G a i j| ≤ B) (hr : ∀ a, ‖w a‖ ≤ R) :
    MemLp (fun a => metricGradientCarrier K (G a) (w a)) 2 μ := by
  apply MemLp.of_bound (metricGradientCarrier_stronglyMeasurable K G hG w hw).aestronglyMeasurable
    (B * metricGradientCarrierConstant K * R)
  apply Filter.Eventually.of_forall
  intro a
  exact (metricGradientCarrier_norm_le K (G a) B hB (hb a) (w a)).trans
    (mul_le_mul_of_nonneg_left (hr a)
      (mul_nonneg hB (metricGradientCarrierConstant_nonneg K)))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Genuine normalized scalar reserves produce the drift and metric pieces of the literal slow flux. -/

def normalizedLiftFluxCrossSource (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → Vec 2 → ℝ) (k : Fin 2) (t : ℝ) (z Y : Vec 2) : ℝ :=
  (Real.exp (A Y))⁻¹ •
    (((Real.sqrt η * v t z k) • (Real.exp (A Y) • f₁ t z Y) -
      Real.sqrt η • ∑ j : Fin 2, G t Y k j •
        AVRegularity.fastPartial j (fun X y => Real.exp (A X) • f₁ t y X) Y z) -
      η • ∑ j : Fin 2, G t Y k j •
        AVRegularity.slowPartial j (fun X y => Real.exp (A X) • f₂ t y X) Y z)

def normalizedLiftFluxCrossReserve (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → Vec 2 → ℝ)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => v t z i))
    (Q₁ : JointSourceReserve (H + 1) f₁) (Q₂ : JointSourceReserve (H + 1) f₂) (k : Fin 2) :
    JointSourceReserve H (normalizedLiftFluxCrossSource A η G v f₁ f₂ k) := by
  let L : ℝ →L[ℝ] ℝ := Real.sqrt η • ContinuousLinearMap.id ℝ ℝ
  let D := ((Qv k).map L).scalarProduct (Q₁.mono H (Nat.le_succ H))
  let F := fun j : Fin 2 => (QG k j).scalarProduct (Q₁.fastPartial H (by omega) j)
  let S := fun j : Fin 2 => (QG k j).scalarProduct (Q₂.covariantSlow H (by omega) A j)
  let LF : ℝ →L[ℝ] ℝ := (-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ
  let LS : ℝ →L[ℝ] ℝ := (-η) • ContinuousLinearMap.id ℝ ℝ
  let R := (D.add ((JointSourceReserve.fintypeSum H _ F).map LF)).add
    ((JointSourceReserve.fintypeSum H _ S).map LS)
  have hd₁ t Y z : DifferentiableAt ℝ (fun y => f₁ t y Y) z :=
    ((Q₁.fast_contDiff t Y).differentiable (by simp)) z
  have hd₂ t z Y : DifferentiableAt ℝ (fun X => f₂ t z X) Y :=
    (((Q₂.regular t).comp₂ contDiff_const contDiff_id).differentiable (by simp)) Y
  refine R.congrSource ?_
  funext t z Y
  have hd : (Real.exp (A Y))⁻¹ •
      ((Real.sqrt η * v t z k) • (Real.exp (A Y) • f₁ t z Y)) =
      (Real.sqrt η * v t z k) • f₁ t z Y := by
    have hc : (Real.exp (A Y))⁻¹ • (Real.exp (A Y) • f₁ t z Y) = f₁ t z Y := by
      rw [smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
    rw [smul_comm, hc]
  have hf j : (Real.exp (A Y))⁻¹ • (G t Y k j •
      AVRegularity.fastPartial j (fun X y => Real.exp (A X) • f₁ t y X) Y z) =
      G t Y k j • AVRegularity.fastPartial j (fun X y => f₁ t y X) Y z := by
    rw [smul_comm, normalized_fastPartial_exp_smul A j f₁ t z Y (hd₁ t Y z)]
  have hs j : (Real.exp (A Y))⁻¹ • (G t Y k j •
      AVRegularity.slowPartial j (fun X y => Real.exp (A X) • f₂ t y X) Y z) =
      G t Y k j • sourceCovariantSlow A j f₂ t z Y := by
    rw [smul_comm, normalized_slowPartial_exp_smul A j f₂ t z Y (hd₂ t z Y)]
  dsimp only [normalizedLiftFluxCrossSource]
  rw [smul_sub, smul_sub, hd]
  rw [smul_comm ((Real.exp (A Y))⁻¹) (Real.sqrt η),
    smul_comm ((Real.exp (A Y))⁻¹) η]
  simp only [Finset.smul_sum, hf, hs]
  simp only [L, LF, LS, smul_apply, ContinuousLinearMap.id_apply,
    sub_eq_add_neg, neg_smul]
  simp only [smul_eq_mul, ← Finset.mul_sum]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite composition budgets for Jacobians close to the identity. -/

theorem operator_comp_close (A B : Vec 2 →L[ℝ] Vec 2) (a b : ℝ)
    (ha : ‖A - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ a)
    (hb : ‖B - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ b) :
    ‖A.comp B - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ a * (1 + b) + b := by
  let I := ContinuousLinearMap.id ℝ (Vec 2)
  have han : 0 ≤ a := (norm_nonneg _).trans ha
  have hB : ‖B‖ ≤ 1 + b := by
    calc
      _ = ‖(B - I) + I‖ := by rw [sub_add_cancel]
      _ ≤ ‖B - I‖ + ‖I‖ := norm_add_le _ _
      _ ≤ b + 1 := by simpa only [I, ContinuousLinearMap.norm_id] using add_le_add hb (le_refl (1 : ℝ))
      _ = _ := add_comm _ _
  have he : A.comp B - I = (A - I).comp B + (B - I) := by
    ext x i
    change A (B x) i - x i = (A (B x) i - B x i) + (B x i - x i)
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul ha hB (norm_nonneg B) han)) hb)

theorem operator_triple_close (A B C : Vec 2 →L[ℝ] Vec 2) (a b c : ℝ)
    (ha : ‖A - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ a)
    (hb : ‖B - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ b)
    (hc : ‖C - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ c) :
    ‖A.comp (B.comp C) - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      (1 + a) * (1 + b) * (1 + c) - 1 := by
  have h := operator_comp_close A (B.comp C) a (b * (1 + c) + c) ha
    (operator_comp_close B C b c hb hc)
  exact h.trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite linear forcing operations preserve a common stored amplitude. -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [SecondCountableTopology E] [SecondCountableTopology F] in
theorem JointSourceReserve.map_uniform_budget {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (L : E →L[ℝ] F) (θ B : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (Q.map L).budget r ≤ θ * (‖L‖ * B) := by
  change ‖L‖ * Q.budget r ≤ _
  exact (mul_le_mul_of_nonneg_left (hQ r hr) (norm_nonneg L)).trans_eq (by ring)

theorem JointSourceReserve.add_uniform_budget {H : ℕ} {f g : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (R : JointSourceReserve H g) (θ B C : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B) (hR : ∀ r ≤ H, R.budget r ≤ θ * C)
    (r : ℕ) (hr : r ≤ H) :
    (Q.add R).budget r ≤ θ * (B + C) := by
  change Q.budget r + R.budget r ≤ _
  exact (add_le_add (hQ r hr) (hR r hr)).trans_eq (mul_add θ B C).symm

theorem JointSourceReserve.fastPartial_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f) (θ B : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) (r : ℕ) (hr : r ≤ R) :
    (Q.fastPartial R hR i).budget r ≤ θ * B := by
  rw [JointSourceReserve.fastPartial_budget]
  exact hQ (1 + r) (by omega)

theorem JointSourceReserve.covariantSlow_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f) (θ B : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (R : ℕ) (hR : 1 + R ≤ H) (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (r : ℕ) (hr : r ≤ R) :
    (Q.covariantSlow R hR A i).budget r ≤ θ * ((1 + ‖A‖) * B) := by
  rw [JointSourceReserve.covariantSlow_budget]
  have hm := mul_le_mul (covariant_scalar_map_norm_le (E := E) A i)
    (hQ r (by omega)) (Q.budget_nonneg r) (norm_nonneg A)
  exact (add_le_add (hQ (1 + r) (by omega)) hm).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Normalized first cross forcing has a bounded genuine joint reserve in both fast coordinates. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def normalizedCellB1Source (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (z Y : Vec 2) : E :=
  (Real.exp (A Y))⁻¹ • AVRegularity.cellB1 η G v t
    (fun X y => Real.exp (A X) • f t y X) Y z

def normalizedCellB1SourceReserve (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => v t z i))
    (Qf : JointSourceReserve (H + 2) f) : JointSourceReserve H (normalizedCellB1Source A η G v f) := by
  let C := fun j : Fin 2 => sourceCovariantSlow A j f
  let QC := fun j : Fin 2 => Qf.covariantSlow (H + 1) (by omega) A j
  let P := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 •
    AVRegularity.fastPartial p.2 (fun X y => f t y X) Y z
  let QP := fun p : Fin 2 × Fin 2 =>
    (QG p.1 p.2).scalarProduct (Qf.fastPartial (H + 1) (by omega) p.2)
  let D := fun (i : Fin 2) t z Y => (Real.sqrt η * v t z i) • C i t z Y
  let Ls : ℝ →L[ℝ] ℝ := Real.sqrt η • ContinuousLinearMap.id ℝ ℝ
  let QD := fun i : Fin 2 => ((Qv i).map Ls).scalarProduct ((QC i).mono H (by omega))
  let SD := JointSourceReserve.fintypeSum H D QD
  let B := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 •
    AVRegularity.fastPartial p.1 (fun X y => C p.2 t y X) Y z + sourceCovariantSlow A p.1 (P p) t z Y
  let QB := fun p : Fin 2 × Fin 2 =>
    (((QG p.1 p.2).mono H (by omega)).scalarProduct ((QC p.2).fastPartial H (by omega) p.1)).add
      ((QP p).covariantSlow H (by omega) A p.1)
  let SB := JointSourceReserve.fintypeSum H B QB
  let L : E →L[ℝ] E := (-Real.sqrt η) • ContinuousLinearMap.id ℝ E
  have hds (t : ℝ) (z X : Vec 2) : DifferentiableAt ℝ (fun Y => f t z Y) X :=
    (((Qf.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hdf (t : ℝ) (Y z : Vec 2) : DifferentiableAt ℝ (fun y => f t y Y) z :=
    ((Qf.fast_contDiff t Y).differentiable (by simp)) z
  have hdC (j : Fin 2) (t : ℝ) (Y z : Vec 2) : DifferentiableAt ℝ (fun y => C j t y Y) z :=
    (((QC j).fast_contDiff t Y).differentiable (by simp)) z
  have hdP (p : Fin 2 × Fin 2) (t : ℝ) (z X : Vec 2) : DifferentiableAt ℝ (fun Y => P p t z Y) X :=
    ((((QP p).regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hslow (j : Fin 2) (t : ℝ) :
      AVRegularity.slowPartial j (fun X y => Real.exp (A X) • f t y X) =
        fun X y => Real.exp (A X) • C j t y X := by
    funext X y
    exact slowPartial_exp_smul A j f t y X (hds t y X)
  have hprod (p : Fin 2 × Fin 2) (t : ℝ) :
      (fun X y => G t X p.1 p.2 • AVRegularity.fastPartial p.2
        (fun Y w => Real.exp (A Y) • f t w Y) X y) =
        fun X y => Real.exp (A X) • P p t y X := by
    funext X y
    rw [fastPartial_exp_smul A p.2 f t y X (hdf t X y)]
    exact smul_comm _ _ _
  have hd (i : Fin 2) (t : ℝ) (z Y : Vec 2) :
      (Real.exp (A Y))⁻¹ • ((Real.sqrt η * v t z i) • AVRegularity.slowPartial i
        (fun X y => Real.exp (A X) • f t y X) Y z) = D i t z Y := by
    rw [smul_comm, normalized_slowPartial_exp_smul A i f t z Y (hds t z Y)]
  have hb (p : Fin 2 × Fin 2) (t : ℝ) (z Y : Vec 2) :
      (Real.exp (A Y))⁻¹ • (G t Y p.1 p.2 • AVRegularity.fastPartial p.1
          (AVRegularity.slowPartial p.2 (fun X y => Real.exp (A X) • f t y X)) Y z +
        AVRegularity.slowPartial p.1 (fun X y => G t X p.1 p.2 •
          AVRegularity.fastPartial p.2 (fun X y => Real.exp (A X) • f t y X) X y) Y z) = B p t z Y := by
    rw [smul_add, smul_comm, hslow, hprod,
      normalized_fastPartial_exp_smul A p.1 (C p.2) t z Y (hdC p.2 t Y z),
      normalized_slowPartial_exp_smul A p.1 (P p) t z Y (hdP p t z Y)]
  have he : normalizedCellB1Source A η G v f =
      fun t z Y => (∑ i : Fin 2, D i t z Y) + L (∑ p : Fin 2 × Fin 2, B p t z Y) := by
    funext t z Y
    change (Real.exp (A Y))⁻¹ • AVRegularity.cellB1 η G v t
      (fun X y => Real.exp (A X) • f t y X) Y z =
      (∑ i : Fin 2, D i t z Y) + (-Real.sqrt η) • (∑ p : Fin 2 × Fin 2, B p t z Y)
    rw [AVRegularity.cellB1, sub_eq_add_neg, smul_add, smul_neg, ← neg_smul, smul_comm]
    simp only [Finset.smul_sum, Fintype.sum_prod_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      exact hd i t z Y
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [neg_smul, smul_neg] using
        congrArg (fun e : E => (-Real.sqrt η) • e) (hb (i, j) t z Y)
  exact (SD.add (SB.map L)).congrSource he.symm
end

/-! The normalized second cross forcing has a genuine bounded reserve without any transverse restriction. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def normalizedCellB2Source (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (t : ℝ) (z Y : Vec 2) : E :=
  (Real.exp (A Y))⁻¹ • AVRegularity.cellB2 η G t
    (fun X y => Real.exp (A X) • f t y X) Y z

def normalizedCellB2SourceReserve (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qf : JointSourceReserve (H + 2) f) : JointSourceReserve H (normalizedCellB2Source A η G f) := by
  let P := fun (p : Fin 2 × Fin 2) t z Y => G t Y p.1 p.2 • sourceCovariantSlow A p.2 f t z Y
  let QP := fun p : Fin 2 × Fin 2 =>
    (QG p.1 p.2).scalarProduct (Qf.covariantSlow (H + 1) (by omega) A p.2)
  let F := fun p : Fin 2 × Fin 2 => sourceCovariantSlow A p.1 (P p)
  let QF := fun p : Fin 2 × Fin 2 => (QP p).covariantSlow H (by omega) A p.1
  let S := JointSourceReserve.fintypeSum H F QF
  let L : E →L[ℝ] E := (-η) • ContinuousLinearMap.id ℝ E
  have hdf (t : ℝ) (z X : Vec 2) : DifferentiableAt ℝ (fun Y => f t z Y) X :=
    (((Qf.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable
      (by simp)) X
  have hdP (p : Fin 2 × Fin 2) (t : ℝ) (z X : Vec 2) :
      DifferentiableAt ℝ (fun Y => P p t z Y) X :=
    ((((QP p).regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable
      (by simp)) X
  have hprod (p : Fin 2 × Fin 2) (t : ℝ) :
      (fun X y => G t X p.1 p.2 • AVRegularity.slowPartial p.2
        (fun Y w => Real.exp (A Y) • f t w Y) X y) =
        fun X y => Real.exp (A X) • P p t y X := by
    funext X y
    rw [slowPartial_exp_smul A p.2 f t y X (hdf t y X)]
    exact smul_comm _ _ _
  have hterm (p : Fin 2 × Fin 2) (t : ℝ) (z Y : Vec 2) :
      (Real.exp (A Y))⁻¹ • AVRegularity.slowPartial p.1
        (fun X y => G t X p.1 p.2 • AVRegularity.slowPartial p.2
          (fun X y => Real.exp (A X) • f t y X) X y) Y z = F p t z Y := by
    rw [hprod]
    exact normalized_slowPartial_exp_smul A p.1 (P p) t z Y (hdP p t z Y)
  have he : normalizedCellB2Source A η G f =
      fun t z Y => L (∑ p : Fin 2 × Fin 2, F p t z Y) := by
    funext t z Y
    change (Real.exp (A Y))⁻¹ • AVRegularity.cellB2 η G t
      (fun X y => Real.exp (A X) • f t y X) Y z = (-η) • (∑ p : Fin 2 × Fin 2, F p t z Y)
    rw [AVRegularity.cellB2, ← neg_smul, smul_comm]
    simp only [Finset.smul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun e : E => (-η) • e) (hterm (i, j) t z Y)
  exact (S.map L).congrSource he.symm
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The molecular diffusion form does not impose the cycle metric's upper bound. -/

/-- The cell-independent molecular matrix acting on weak first derivatives. -/
def molecularDiffusionForm (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ :=
  -∑ j : Fin 2, ∑ k : Fin 2,
    (G t j k) • pullbackInnerCLM (cellDerivativeCLM j) (cellDerivativeCLM k)

theorem molecularDiffusionForm_apply (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    molecularDiffusionForm G t u z =
      -∑ j : Fin 2, ∑ k : Fin 2,
        G t j k * inner ℝ (cellDerivativeCLM j u) (cellDerivativeCLM k z) := by
  simp [molecularDiffusionForm, pullbackInnerCLM_apply]

theorem molecularDiffusionForm_pairing_measurable (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, Measurable (fun t => G t i j)) (u z : TorusHk 1 ℂ) :
    Measurable (fun t => molecularDiffusionForm G t u z) := by
  simp only [molecularDiffusionForm_apply]
  exact (Finset.measurable_sum _ (fun j _ =>
    Finset.measurable_sum _ (fun k _ => (hG j k).mul measurable_const))).neg

theorem molecularDiffusionForm_abs_le (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (CG : ℝ) (hG : ∀ t i j, |G t i j| ≤ CG)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    |molecularDiffusionForm G t u z| ≤
      ∑ j : Fin 2, ∑ k : Fin 2,
        CG * ‖cellDerivativeCLM j u‖ * ‖cellDerivativeCLM k z‖ := by
  rw [molecularDiffusionForm_apply, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)).trans
    (by simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right (hG t j k)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))))

/-- The real quadratic lower bound also controls complex gradients, even for a
non-symmetric molecular matrix. -/
theorem molecularMetric_complex_coercive (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
      ∑ i, ∑ j, G t i j * k i * k j) (t : ℝ) (w : Fin 2 → ℂ) :
    (3 / 4) * ∑ i, ‖w i‖ ^ 2 ≤
      (∑ i, ∑ j, (G t i j : ℂ) * w i * star (w j)).re := by
  have hr := hG t (fun i => (w i).re)
  have hi := hG t (fun i => (w i).im)
  have he (i : Fin 2) : ‖w i‖ ^ 2 = (w i).re ^ 2 + (w i).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp [Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, he] at *
  nlinarith

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Fast metric flux and the slow metric flux of a centered predecessor have zero cell mean. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem liftFluxCross_cell_mean (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : Vec 2 → Vec 2) (Φ Ψ : Vec 2 → Vec 2 → E)
    (hG : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun Y => G Y i j))
    (hv : Continuous v) (hΦ : GoodField 1 Φ) (hΨ : CoefField True 1 Ψ)
    (Y : Vec 2) (k : Fin 2) :
    fieldCellMean (fun z =>
      (((Real.sqrt η * v z k) • Φ Y z -
        Real.sqrt η • ∑ j : Fin 2, G Y k j • fastPartial j Φ Y z) -
        η • ∑ j : Fin 2, G Y k j • slowPartial j Ψ Y z)) =
      fieldCellMean (fun z => (Real.sqrt η * v z k) • Φ Y z) := by
  have hF : CoefField True 0 (fun Y z =>
      Real.sqrt η • ∑ j : Fin 2, G Y k j • fastPartial j Φ Y z) :=
    (CoefField.sum Finset.univ (fun j _ =>
      (GoodField.cent_fastPartial (c := True) hΦ j).mulX (hG k j))).smul (Real.sqrt η)
  have hS : CoefField True 0 (fun Y z =>
      η • ∑ j : Fin 2, G Y k j • slowPartial j Ψ Y z) :=
    (CoefField.sum Finset.univ (fun j _ => (hΨ.slowPartial j).mulX (hG k j))).smul η
  have hD : Continuous (fun z => (Real.sqrt η * v z k) • Φ Y z) :=
    (continuous_const.mul ((continuous_apply k).comp hv)).smul (hΦ.continuous_slice Y)
  let d : Vec 2 → E := fun z => (Real.sqrt η * v z k) • Φ Y z
  let f : Vec 2 → E := fun z => Real.sqrt η • ∑ j : Fin 2, G Y k j • fastPartial j Φ Y z
  let s : Vec 2 → E := fun z => η • ∑ j : Fin 2, G Y k j • slowPartial j Ψ Y z
  change fieldCellMean ((d - f) - s) = fieldCellMean d
  have hf0 : fieldCellMean f = 0 := hF.2 trivial Y
  have hs0 : fieldCellMean s = 0 := hS.2 trivial Y
  calc
    fieldCellMean ((d - f) - s) = fieldCellMean (d - f) - fieldCellMean s :=
      fieldCellMean_sub (hD.sub (hF.1.continuous_slice Y)) (hS.1.continuous_slice Y)
    _ = (fieldCellMean d - fieldCellMean f) - fieldCellMean s :=
      congrArg (fun x => x - fieldCellMean s) (fieldCellMean_sub hD (hF.1.continuous_slice Y))
    _ = fieldCellMean d := by rw [hf0, hs0, sub_zero, sub_zero]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The higher metric carrier represents exactly the literal metric-gradient flux. -/

theorem metricEntryGradient_value_ae (K : ℕ) (i j : Fin 2) (w : TorusHk (K + 1) ℂ) :
    torusHkValueCLM (metricEntryGradientCLM K i j w) =ᵐ[
      volume.restrict AVenhance.unitCube]
      fun x => metricEntryFiberCLM i j ((torusHkValueCLM (torusGradientTensor w)) x) := by
  change (metricEntryGradientCLM K i j w).val (valueIndex2 K) =ᵐ[_]
    (fun x => metricEntryFiberCLM i j ((torusGradientTensor w).val (valueIndex2 K) x))
  simpa only [metricEntryGradientCLM, ContinuousLinearMap.comp_apply,
    mapTorusHkCLM_apply, torusGradientTensorCLM_apply] using
    mapTorusHk_jet_ae (metricEntryFiberCLM i j) (torusGradientTensor w) (valueIndex2 K)

theorem metricEntryFiber_sum (A : Matrix (Fin 2) (Fin 2) ℝ) (v : ComplexCellVector) :
    (∑ i : Fin 2, ∑ j : Fin 2, A i j • metricEntryFiberCLM i j v) =
      cellMetricFluxVector A v := by
  apply PiLp.ext
  intro k
  fin_cases k <;>
    simp [Fin.sum_univ_two, metricEntryFiberCLM, vectorSlotCLM, cellMetricFluxVector,
      Complex.real_smul]

theorem metricGradientCarrier_value_ae (K : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (w : TorusHk (K + 1) ℂ) :
    torusHkValueCLM (metricGradientCarrier K A w) =ᵐ[
      volume.restrict AVenhance.unitCube]
      fun x => cellMetricFluxVector A ((torusHkValueCLM (torusGradientTensor w)) x) := by
  unfold Matrix at A
  let L := torusHkValueCLM (E := ComplexCellVector) (K := K)
  have he : torusHkValueCLM (metricGradientCarrier K A w) =
      ∑ i : Fin 2, ∑ j : Fin 2, A i j • torusHkValueCLM (metricEntryGradientCLM K i j w) := by
    change L (∑ i : Fin 2, ∑ j : Fin 2, A i j • metricEntryGradientCLM K i j w) = _
    have hsum (f : Fin 2 → TorusHk K ComplexCellVector) : L (∑ i, f i) = ∑ i, L (f i) :=
      map_sum L.toLinearMap f Finset.univ
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j _
    exact L.map_smul (A i j) _
  rw [he]
  have hh (i : Fin 2) :
      (∑ j : Fin 2, A i j • torusHkValueCLM (metricEntryGradientCLM K i j w)) =ᵐ[
        volume.restrict AVenhance.unitCube]
        fun x => ∑ j : Fin 2, A i j •
          metricEntryFiberCLM i j ((torusHkValueCLM (torusGradientTensor w)) x) := by
    apply (Lp.coeFn_finsetSum _ _).trans
    have hh := eventuallyEq_sum (s := Finset.univ) (fun j (_ : j ∈ Finset.univ) =>
      (Lp.coeFn_smul (A i j) (torusHkValueCLM (metricEntryGradientCLM K i j w))).trans
        ((metricEntryGradient_value_ae K i j w).fun_comp (fun v => A i j • v)))
    have heq : (∑ j : Fin 2, (fun v => A i j • v) ∘
        (fun x => metricEntryFiberCLM i j ((torusHkValueCLM (torusGradientTensor w)) x))) =
        (fun x => ∑ j : Fin 2, A i j •
          metricEntryFiberCLM i j ((torusHkValueCLM (torusGradientTensor w)) x)) := by
      funext x
      simp only [Finset.sum_apply, Function.comp_apply]
    exact hh.trans (Filter.EventuallyEq.of_eq heq)
  apply (Lp.coeFn_finsetSum _ _).trans
  have ha := eventuallyEq_sum (s := Finset.univ) (fun i _ => hh i)
  have hb := ha.trans (Filter.EventuallyEq.of_eq
    (funext (fun x => metricEntryFiber_sum A ((torusHkValueCLM (torusGradientTensor w)) x))))
  simpa only [Finset.sum_fn] using hb

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Actual scalar left coefficients act on normalized coarse fields through finite bounded words. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedLiftApplySource (n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → ι → ℝ) (v : ι)
    (t : ℝ) (z Y : Vec 2) : ℝ :=
  (Real.exp (A Y))⁻¹ • liftApply n c
    (fun t X => Real.exp (A X) • f t X) t Y z v
end

/-! One maximal-order price controls all requested factorial coefficient seminorms. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weak_constituentPhysical_uniform_coefficientSeminorm (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (d Ks k : ℕ) (hk : k ≤ Ks) (ρ B : ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hgs : ∀ t p, t ∈ (F.piece p).output →
      ContDiff ℝ (Ks : ℕ) (weakPhysicalPieceCoefficient F ν e E actual v u γ d t p))
    (hjet : ∀ t p, t ∈ (F.piece p).output → ∀ r, r ≤ Ks → ∀ x,
      ρ ^ r * ‖iteratedFDeriv ℝ r
        (weakPhysicalPieceCoefficient F ν e E actual v u γ d t p) x‖ ≤ B)
    (t₀ t₁ : ℝ) :
    coefficientSeminorm ρ k t₀ t₁ (constituentPhysical F ν e E actual v u γ d) ≤
      ENNReal.ofReal (((Ks + 1 : ℕ) * (2 : ℝ) ^ Ks) * B) := by
  apply CycleJointProofs.uniform_pointwise_coefficient_seminorm ρ hρ k Ks hk t₀ t₁
    (constituentPhysical F ν e E actual v u γ d)
    (fun t _ => (weak_constituentPhysical_spatial_contDiff F ν e E actual v u γ d Ks t (hgs t)).of_le
      (by exact_mod_cast hk)) B hB
  intro t _ r hr x
  exact weak_constituentPhysical_jet_assembly F ν e E actual v u γ d r ρ B hρ.le hB t
    (fun p hp => (hgs t p hp).of_le (by exact_mod_cast hr.trans hk))
    (fun p hp => hjet t p hp r (hr.trans hk)) x
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Coarse charts have scale-independent positive jets at every finer spatial scale. -/

theorem scale_ratio_derivative_bound (ρ e : ℝ) (hρ : 0 < ρ) (he : 0 < e)
    (hρe : ρ ≤ e) (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (V : ℝ)
    (hV : V ≤ C * (e⁻¹) ^ n) : ρ ^ n * V ≤ C := by
  calc
    ρ ^ n * V ≤ ρ ^ n * (C * (e⁻¹) ^ n) :=
      mul_le_mul_of_nonneg_left hV (pow_nonneg hρ.le _)
    _ = C * (ρ * e⁻¹) ^ n := by rw [mul_pow]; ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by positivity) ((mul_le_mul_of_nonneg_right hρe (inv_nonneg.mpr he.le)).trans_eq
        (mul_inv_cancel₀ he.ne')) ) hC
    _ = C := mul_one _

theorem scaled_coarse_flow_derivative_norm (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (m : ℕ) (hm : 1 ≤ m) (r t : ℝ)
    (ht : |t - r| ≤ 2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ m)⁻¹)
    (ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ D.eps m) (y y' : Vec 2)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun z => ρ⁻¹ • (D.flowOf m t (y' + ρ • z) r - y)) x‖ ≤
      (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 : ℝ) ^ (n - 1)) := by
  have he : 0 < D.eps m := Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ D.Λ)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => D.flowOf m t z r) :=
    CycleReference.streamFlow_spatial_smooth (D.hΦ m) t r
  rw [CycleWords.cell_rescaled_iteratedFDeriv_norm _ hs ρ hρ y y' n hn x]
  apply scale_ratio_derivative_bound ρ (D.eps m) hρ he hρe (n - 1)
    ((2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 : ℝ) ^ (n - 1))) (by positivity)
  have hb := actual_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
    m hm r t ht n hn (y' + ρ • x)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * n.factorial * (2 ^ 14 * (D.eps m)⁻¹) ^ (n - 1)) := hb
    _ = _ := by rw [mul_pow]; ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Componentwise normalized left application retains each incoming matrix entry budget. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedLiftApplyComponentReserve (H n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      JointSourceReserve H (fun t z Y => c m.val α t Y z v u 1))
    (Qf : ∀ u : ι, JointSourceReserve (H + n) (fun t _ Y => f t Y u)) :
    JointSourceReserve H (normalizedLiftApplySource n c A f v) := by
  let Qwhole := jointSourcePiReserve (H + n) (fun u t _ Y => f t Y u) Qf
  let F := fun (m : Fin (n + 1)) (α : DerivativeWord2 m.val) (u : ι) t z Y =>
    c m.val α t Y z v u 1 •
      sourceCovariantWord A (fun t _ Y => f t Y u) m.val α t z Y
  let Q := fun (m : Fin (n + 1)) (α : DerivativeWord2 m.val) (u : ι) =>
    (Qc m α u).scalarProduct
      ((Qf u).covariantWord
        m.val H (by omega) A α)
  let S := JointSourceReserve.fintypeSum H
    (fun m t z Y => ∑ α : DerivativeWord2 m.val, ∑ u : ι, F m α u t z Y)
    (fun m => JointSourceReserve.fintypeSum H
      (fun α t z Y => ∑ u : ι, F m α u t z Y)
      (fun α => JointSourceReserve.fintypeSum H (F m α) (Q m α)))
  have he : normalizedLiftApplySource n c A f v =
      fun t z Y => ∑ m : Fin (n + 1), ∑ α : DerivativeWord2 m.val,
        ∑ u : ι, F m α u t z Y := by
    funext t z Y
    unfold normalizedLiftApplySource liftApply
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro u _
    have hreg : ContDiff ℝ (m.val : ℕ∞) (fun X => Real.exp (A X) • f t X) :=
      (Real.contDiff_exp.comp A.contDiff).smul
        (((Qwhole.regular t).comp₂ (contDiff_const (c := (0 : Vec 2))) contDiff_id).of_le
          (by exact_mod_cast (show m.val ≤ H + n by omega)))
    rw [ChartTransport.orderedDerivative_apply α hreg u Y]
    simp only [Pi.smul_apply]
    have hd := orderedDerivative_exp_smul_covariantWord
      (Qf u)
      m.val (by omega) A α t z Y
    rw [hd]
    change (Real.exp (A Y))⁻¹ • c m.val α t Y z v u
      (Real.exp (A Y) • sourceCovariantWord A (fun t _ Y => f t Y u) m.val α t z Y) = _
    rw [map_smul, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
    have hc (x : ℝ) : c m.val α t Y z v u x = x • c m.val α t Y z v u 1 := by
      simpa only [smul_eq_mul, mul_one] using (c m.val α t Y z v u).map_smul x 1
    rw [hc]
    change sourceCovariantWord A (fun t _ Y => f t Y u) m.val α t z Y *
      c m.val α t Y z v u 1 = c m.val α t Y z v u 1 *
        sourceCovariantWord A (fun t _ Y => f t Y u) m.val α t z Y
    exact mul_comm _ _
  exact S.congrSource he.symm

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Molecular diffusion and the bounded drift as an actual cell Hilbert generator. -/

def molecularCoefficients (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) : CellCoefficients := ⟨fun t _ => G t, v, 0, 0⟩

def molecularGeneratorForm (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) (t : ℝ) :
    TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ :=
  molecularDiffusionForm G t - ∑ j : Fin 2,
    pullbackInnerCLM
      ((cellDriftEntryCLM (molecularCoefficients G v) V hv hb t j).comp
        (cellDerivativeCLM j)) torusHkValueCLM

def molecularGeneratorB (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) (t : ℝ) :
    TorusHk 1 ℂ →ₗ[ℝ] TorusHk 1 ℂ →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp (molecularGeneratorForm G v V hv hb t).toLinearMap

theorem molecularGeneratorForm_pairing_stronglyMeasurable
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hG : ∀ i j, Measurable (fun t => G t i j))
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (u z : TorusHk 1 ℂ) :
    StronglyMeasurable (fun t => molecularGeneratorForm G v V hv hb t u z) := by
  simp only [molecularGeneratorForm, Fin.sum_univ_two, sub_apply, add_apply,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  exact (molecularDiffusionForm_pairing_measurable G hG u z).stronglyMeasurable.sub
    ((cellDrift_pairing_stronglyMeasurable (molecularCoefficients G v) V hv hb 0 _ _).add
      (cellDrift_pairing_stronglyMeasurable (molecularCoefficients G v) V hv hb 1 _ _))

theorem molecularGeneratorForm_abs_le
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (CG V : ℝ)
    (hG : ∀ t i j, |G t i j| ≤ CG)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    |molecularGeneratorForm G v V hv hb t u z| ≤
      (∑ j : Fin 2, ∑ k : Fin 2, CG * ‖cellDerivativeCLM j u‖ * ‖cellDerivativeCLM k z‖) +
      ∑ j : Fin 2, |V| * ‖cellDerivativeCLM j u‖ * ‖torusHkValueCLM z‖ := by
  have hd := molecularDiffusionForm_abs_le G CG hG t u z
  simp only [molecularGeneratorForm, sub_apply, sum_apply,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  apply (abs_sub _ _).trans
  apply add_le_add hd
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun j _ =>
    cellDrift_pairing_abs_le (molecularCoefficients G v) V hv hb t j _ _)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! A time-uniform H¹ operator norm for the molecular generator. -/

theorem molecularGeneratorForm_uniform_norm_bound
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (CG V : ℝ)
    (hG : ∀ t i j, |G t i j| ≤ CG)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t u, ‖molecularGeneratorForm G v V hv hb t u‖ ≤ M * ‖u‖ := by
  let D := fun j => ‖cellDerivativeCLM j‖
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let M := (∑ j : Fin 2, ∑ k : Fin 2, CG * D j * D k) +
    ∑ j : Fin 2, |V| * D j * J
  have hCG : 0 ≤ CG := (abs_nonneg (G 0 0 0)).trans (hG 0 0 0)
  have hM : 0 ≤ M := by dsimp only [M, D, J]; positivity
  refine ⟨M, hM, fun t u => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg u))
  intro z
  rw [Real.norm_eq_abs]
  apply (molecularGeneratorForm_abs_le G v CG V hG hv hb t u z).trans
  have hd (j : Fin 2) := (cellDerivativeCLM j).le_opNorm u
  have ht (j : Fin 2) := (cellDerivativeCLM j).le_opNorm z
  have hjz := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm z
  calc
    _ ≤ (∑ j : Fin 2, ∑ k : Fin 2, CG * (D j * ‖u‖) * (D k * ‖z‖)) +
        ∑ j : Fin 2, |V| * (D j * ‖u‖) * (J * ‖z‖) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => by
          dsimp only [D]; gcongr
          · exact hd j
          · exact ht k))
      · exact Finset.sum_le_sum (fun j _ => by
          dsimp only [D, J]; gcongr
          exact hd j)
    _ = M * ‖u‖ * ‖z‖ := by dsimp only [M]; simp only [Fin.sum_univ_two]; ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The second cross forcing preserves a single amplitude with a constant fixed by the finite derivative menu. -/

noncomputable def normalizedCellB2UniformBudget (H : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BF : ℝ) : ℝ :=
  (Fintype.card (Fin 2 × Fin 2) : ℝ) * ‖(-η) • ContinuousLinearMap.id ℝ ℝ‖ *
    ((1 + ‖A‖) * (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ (H + 1) * BG *
      ((1 + ‖A‖) * BF)))

theorem normalizedCellB2UniformBudget_nonneg (H : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BF : ℝ) (hBG : 0 ≤ BG) (hBF : 0 ≤ BF) :
    0 ≤ normalizedCellB2UniformBudget H A η BG BF := by
  unfold normalizedCellB2UniformBudget
  positivity

/-! The literal slow-flux cross terms preserve an individual stored amplitude. -/

def normalizedLiftFluxCrossBudget (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η BG BV BF₁ BF₂ : ℝ) : ℝ :=
  let T := ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H
  T * (‖Real.sqrt η • ContinuousLinearMap.id ℝ ℝ‖ * BV) * BF₁ +
    ‖(-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ‖ *
      ((Fintype.card (Fin 2) : ℝ) * (T * BG * BF₁)) +
    ‖(-η) • ContinuousLinearMap.id ℝ ℝ‖ *
      ((Fintype.card (Fin 2) : ℝ) * (T * BG * ((1 + ‖A‖) * BF₂)))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Source operators depend only on the slow germ of their input, uniformly in the fast phase. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SlowOpenFieldEq (U : Set (Vec 2)) (f g : Vec 2 → Vec 2 → E) : Prop :=
  ∀ X ∈ U, ∀ z, f X z = g X z

theorem SlowOpenFieldEq.fastPartial {U : Set (Vec 2)}
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g) (i : Fin 2) :
    SlowOpenFieldEq U (AVRegularity.fastPartial i f) (AVRegularity.fastPartial i g) := by
  intro X hX z
  have hf : f X = g X := funext (he X hX)
  rw [AVRegularity.fastPartial, AVRegularity.fastPartial, hf]

theorem SlowOpenFieldEq.slowPartial {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g) (i : Fin 2) :
    SlowOpenFieldEq U (AVRegularity.slowPartial i f) (AVRegularity.slowPartial i g) := by
  intro X hX z
  have hh : (fun Y => f Y z) =ᶠ[𝓝 X] fun Y => g Y z := by
    filter_upwards [hU.mem_nhds hX] with Y hY
    exact he Y hY z
  exact congrArg (fun L : Vec 2 →L[ℝ] E => L (basisVec i)) hh.fderiv_eq

theorem SlowOpenFieldEq.dEps {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g) (η ε : ℝ) (i : Fin 2) :
    SlowOpenFieldEq U (AVRegularity.dEps η ε i f) (AVRegularity.dEps η ε i g) := by
  intro X hX z
  exact congrArg₂ (fun a b : E => a + (Real.sqrt η * ε) • b)
    (he.fastPartial i X hX z) (he.slowPartial hU i X hX z)

theorem SlowOpenFieldEq.dEpsWord {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g)
    (η ε : ℝ) {n : ℕ} (α : DerivativeWord2 n) :
    SlowOpenFieldEq U (AVRegularity.dEpsWord η ε α f) (AVRegularity.dEpsWord η ε α g) := by
  have main : ∀ w : List (Fin 2), SlowOpenFieldEq U
      (w.foldl (fun f i => AVRegularity.dEps η ε i f) f)
      (w.foldl (fun f i => AVRegularity.dEps η ε i f) g) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact he
    | append_singleton w i ih =>
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact ih.dEps hU η ε i
  exact main (List.ofFn α)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem SlowOpenFieldEq.sourceFlux {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → ∀ i, h i} (he : SlowOpenFieldEq U f g)
    (edge : ConstituentEdges D h) (η ε t : ℝ) (k : Fin 2) :
    SlowOpenFieldEq U (sourceFlux edge η ε t f k) (sourceFlux edge η ε t g k) := by
  intro X hX z
  funext v
  unfold AVRegularity.sourceFlux
  simp_rw [he.dEpsWord hU η ε _ X hX z]

theorem SlowOpenFieldEq.sourceCoeff {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → ∀ i, h i} (he : SlowOpenFieldEq U f g)
    (edge : ConstituentEdges D h) (η t : ℝ) (j : ℕ) :
    SlowOpenFieldEq U (sourceCoeff edge η j t f) (sourceCoeff edge η j t g) := by
  intro X hX z
  have hs : (fun ε => sourceOp edge η ε t f X z) =
      fun ε => sourceOp edge η ε t g X z := by
    funext ε
    unfold sourceOp
    apply Finset.sum_congr rfl
    intro k _
    exact ((he.sourceFlux hU edge η ε t k).dEps hU η ε k) X hX z
  unfold AVRegularity.sourceCoeff
  rw [hs]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Coefficient hypotheses for the existing finite cell mass inversion. -/

theorem molecularGalerkinOperator_aestronglyMeasurable
    (N : ℕ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hG : ∀ i j, Measurable (fun t => G t i j))
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    AEStronglyMeasurable
      (fun t => cellGalerkinOperator N (molecularGeneratorB G v V hv hb t)) volume := by
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  apply weakMassGeneratorCLM_aestronglyMeasurable basis
    (cellGalerkinMass N) (cellGalerkinMass_injective N)
    (fun t => cellGalerkinForm N (molecularGeneratorB G v V hv hb t))
  intro i j
  exact (molecularGeneratorForm_pairing_stronglyMeasurable G v V hG hv hb
    (basis j).val (basis i).val).aestronglyMeasurable

theorem molecularGalerkinOperator_bounded
    (N : ℕ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (CG V : ℝ)
    (hG : ∀ t i j, |G t i j| ≤ CG)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖cellGalerkinOperator N (molecularGeneratorB G v V hv hb t)‖ ≤ M := by
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  let entry := fun i j =>
    (∑ r : Fin 2, ∑ k : Fin 2,
      CG * ‖cellDerivativeCLM r (basis j).val‖ * ‖cellDerivativeCLM k (basis i).val‖) +
    ∑ r : Fin 2, |V| * ‖cellDerivativeCLM r (basis j).val‖ *
      ‖torusHkValueCLM (basis i).val‖
  let M := ∑ i, ∑ j, entry i j *
    ‖weakMassGeneratorCLM (cellGalerkinMass N) (cellGalerkinMass_injective N)
      (weakRankOneForm basis i j)‖
  have hCG : 0 ≤ CG := (abs_nonneg (G 0 0 0)).trans (hG 0 0 0)
  have he : ∀ i j, 0 ≤ entry i j := by
    intro i j
    dsimp only [entry]
    positivity
  refine ⟨M, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (he i j) (norm_nonneg _)))
  · intro t
    apply weakMassGeneratorCLM_norm_le basis
      (cellGalerkinMass N) (cellGalerkinMass_injective N)
      (cellGalerkinForm N (molecularGeneratorB G v V hv hb t)) entry
    intro i j
    exact molecularGeneratorForm_abs_le G v CG V hG hv hb t (basis j).val (basis i).val

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The first cross forcing preserves its scalar stored amplitude through every divergence term. -/

def normalizedCellB1UniformBudget (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η BG BV BF : ℝ) : ℝ :=
  (Fintype.card (Fin 2) : ℝ) *
    (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H *
      (‖Real.sqrt η • ContinuousLinearMap.id ℝ ℝ‖ * BV) * ((1 + ‖A‖) * BF)) +
  ‖(-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ‖ * (Fintype.card (Fin 2 × Fin 2) : ℝ) *
    (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H * BG * ((1 + ‖A‖) * BF) +
      (1 + ‖A‖) * (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ (H + 1) * BG * BF))

theorem normalizedCellB1UniformBudget_nonneg (H : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BF : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBF : 0 ≤ BF) :
    0 ≤ normalizedCellB1UniformBudget H A η BG BV BF := by
  unfold normalizedCellB1UniformBudget
  positivity

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

/-! Both cross operators depend only on the slow open germ of their fast fields. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SlowOpenFieldEq.cellB1 {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g)
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) :
    SlowOpenFieldEq U (AVRegularity.cellB1 η G v t f) (AVRegularity.cellB1 η G v t g) := by
  intro X hX z
  unfold AVRegularity.cellB1
  apply congrArg₂ (fun a b : E => a - Real.sqrt η • b)
  · apply Finset.sum_congr rfl
    intro i _
    rw [he.slowPartial hU i X hX z]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(he.slowPartial hU j).fastPartial i X hX z]
    have hp : SlowOpenFieldEq U
        (fun Y y => G t Y i j • AVRegularity.fastPartial j f Y y)
        (fun Y y => G t Y i j • AVRegularity.fastPartial j g Y y) := by
      intro Y hY y
      exact congrArg (fun w : E => G t Y i j • w) (he.fastPartial j Y hY y)
    rw [hp.slowPartial hU i X hX z]

theorem SlowOpenFieldEq.cellB2 {U : Set (Vec 2)} (hU : IsOpen U)
    {f g : Vec 2 → Vec 2 → E} (he : SlowOpenFieldEq U f g)
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) :
    SlowOpenFieldEq U (AVRegularity.cellB2 η G t f) (AVRegularity.cellB2 η G t g) := by
  intro X hX z
  unfold AVRegularity.cellB2
  apply congrArg (fun a : E => -(η • a))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hp : SlowOpenFieldEq U
      (fun Y y => G t Y i j • AVRegularity.slowPartial j f Y y)
      (fun Y y => G t Y i j • AVRegularity.slowPartial j g Y y) := by
    intro Y hY y
    exact congrArg (fun w : E => G t Y i j • w) (he.slowPartial hU j Y hY y)
  exact hp.slowPartial hU i X hX z

end AVRegularity.EntryWeakProofs
end
end
