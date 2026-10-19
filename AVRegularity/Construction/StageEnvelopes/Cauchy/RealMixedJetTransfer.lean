-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.StageEnvelopes.Assembly
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Proofs.ComplexContext.DSlowCell
public import AVRegularity.Proofs.ComplexContext.RecCMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.RingTheory.PicardGroup

section
section
/-! The shared context Cauchy estimate before radius normalization and finite menu sums.
All constants precede Dm. The only analytic leaf is a mixed jet bound on the actual carrier. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

/-- The number of ordered scalar words in the actual source-order menu. -/
def originalWordCount (cap : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 2 cap, Fintype.card (DerivativeWord2 (d - 1))

/-- A finite analytic jet menu, independent of the ambient order cap. -/
def analyticCost (p : ContextEnvelopeParameters) (A : ℝ) : ℝ :=
  ((originalWordCount p.Dstar * (p.Kan + 1) * (p.Lan + 1) : ℕ) : ℝ) * A

/-- A coarse bound for every molecular factorial and every triangular jet menu. -/
def molecularCost (p : ContextEnvelopeParameters) (A : ℝ) : ℝ :=
  ((originalWordCount p.Dstar * (p.Ks + 1) ^ 2 * (p.Ks + p.Dstar).factorial : ℕ) : ℝ) * A

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ}

/-- Pointwise Cauchy jets of one identity before incidence summation. A constant scalar
multiple is included so that marking and dimensionalization use this same analytic estimate.
The source-size factor is exactly the one recorded by IsContextCertified. -/
structure ContextCarrierJetBounds (G : GenStage D hr Dm b j₀) (k : InvConsts)
    (W : Set ℝ) (mres A : ℝ) : Prop where
  smooth : G.fam.IsSmoothOn (G.innerDomain W mres) (D.eps (G.level - 1))
    (fun _ => max (k.Kan + k.Lan) (k.Ks + k.Jm))
  jet : ∀ v u (γ : G.fam.Γ v u) d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
    ∀ (I : DerivativeWord2 (d - 1)) r q,
    r ≤ max k.Kan (k.Ks + k.Jm) → q ≤ max k.Lan k.Ks → ∀ a : ℝ,
      pointwiseJetSupFam (fun x : G.fam.Index => G.innerDomain W mres x.1 x.2) r q
        (fun x t Y z => a • G.fam.slowFlux (D.eps (G.level - 1)) x.1 x.2 v u γ d I t Y z) ≤
      ENNReal.ofReal (|a| * (A * (G.fam.identity v u γ).record.size) *
        ((G.fam.identity v u γ).record.length / D.eps G.level) ^ (d - 2) /
          (D.eps (G.level - 1)) ^ r)

/-- Cauchy in the recentered slow carrier and Fourier differentiation in the final
phase, uniformly over all histories, slots and actual output times. The coefficient's mode
bounds are supplied by ContextEnvelopeInput.certified; this is not a native-chart assertion. -/
def ContextCarrierScaledJetStatement : Prop :=
  ∀ p : ContextEnvelopeParameters, ∃ (A : ℝ) (mStar : ℕ), 0 ≤ A ∧
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    (D : OCData) (Dm j₀ : ℕ) (b : ℝ) (G : GenStage D hr Dm b j₀) (k : InvConsts) (mres ρ : ℝ),
    ContextEnvelopeInput p G k mres ρ → mStar ≤ G.level → ∀ W : Set ℝ,
      ContextCarrierJetBounds G k W mres A

/-- The scalar radius inequalities and finite menu sums, with the exact
factorial weights. Both time-supremum conventions use the same constants. -/
def MolecularRadiusSummationStatement : Prop :=
  ∀ (p : ContextEnvelopeParameters) (A : ℝ), 0 ≤ A →
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    (D : OCData) (Dm j₀ : ℕ) (b : ℝ) (G : GenStage D hr Dm b j₀) (k : InvConsts) (mres ρ : ℝ),
    ContextEnvelopeInput p G k mres ρ → analyticCost p A ≤ k.Ca →
    (∀ j, molecularCost p A ≤ k.Cm j) → ∀ W : Set ℝ,
    ContextCarrierJetBounds G k W mres A →
    ∀ w : CompIn G.comps → ℝ, (∀ v, 0 < w v) → ContextConstituentBounds G k W mres ρ w

/-- ROUTINE: essential time suprema never exceed genuine suprema, without measurability
or a positive-measure time window assumption. -/
def PointwiseEssentialComparisonStatement : Prop :=
  ∀ (ι : Type*) (dom : ι → Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2), jetSupFam dom r q f ≤ pointwiseJetSupFam dom r q f

/-- ROUTINE: the word count uses only the actual order bound, never Dm. -/
def OriginalOrderMenuStatement : Prop :=
  ∀ (cap actual : ℕ), actual ≤ cap → ∀ (B : ℝ≥0∞)
    (f : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ≥0∞),
    (∀ d ∈ Finset.Icc 2 actual, ∀ I, f d I ≤ B) →
      (∑ d ∈ Finset.Icc 2 actual, ∑ I, f d I) ≤ (originalWordCount cap : ℝ≥0∞) * B

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Supremum comparison and actual original-order counting. Neither uses a time continuity
hypothesis, a nonempty family, or the ambient tensor cap Dm. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

theorem pointwise_essential_comparison : PointwiseEssentialComparisonStatement := by
  intro ι dom r q f
  exact iSup_mono fun _ => essSup_le_iSup

theorem envelopeJetSup_le_pointwise {ι : Type*} (dom : ι → Set (ℝ × Vec 2))
    (r q : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) (pointwise : Bool) :
    envelopeJetSup pointwise dom r q f ≤ pointwiseJetSupFam dom r q f := by
  cases pointwise
  · exact pointwise_essential_comparison ι dom r q f
  · exact le_rfl

theorem original_order_menu : OriginalOrderMenuStatement := by
  classical
  intro cap actual hcap B f hf
  calc
    _ ≤ ∑ d ∈ Finset.Icc 2 actual, ∑ _I : DerivativeWord2 (d - 1), B :=
      Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun I _ => hf d hd I
    _ ≤ ∑ d ∈ Finset.Icc 2 cap, ∑ _I : DerivativeWord2 (d - 1), B :=
      Finset.sum_le_sum_of_subset fun d hd =>
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hcap⟩
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, originalWordCount,
        Nat.cast_sum, Finset.sum_mul]

/-- The triangular molecular menu is contained in its square, including order zero. -/
theorem triangular_jet_sum_le (k cap : ℕ) (hcap : k ≤ cap) (B : ℝ≥0∞)
    (f : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ r ∈ Finset.range (k + 1), ∀ q ∈ Finset.range (k + 1 - r), f r q ≤ B) :
    (∑ r ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1 - r), f r q) ≤
      (((cap + 1) ^ 2 : ℕ) : ℝ≥0∞) * B := by
  calc
    _ ≤ ∑ r ∈ Finset.range (k + 1), ∑ _q ∈ Finset.range (k + 1 - r), B :=
      Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun q hq => hf r hr q hq
    _ ≤ ∑ _r ∈ Finset.range (cap + 1), ∑ _q ∈ Finset.range (cap + 1), B := by
      apply le_trans (Finset.sum_le_sum fun r _ =>
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega : k + 1 - r ≤ cap + 1)))
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, Nat.cast_mul,
        mul_assoc]

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Scalar normalization of Cauchy jets. All powers here are natural powers; the analytic
stream and fractional scale estimates do not enter this algebra. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

/-- An original quadratic order has no birth-length factor. -/
theorem length_ratio_pow_le_one {R e : ℝ} (hR : 0 ≤ R) (he : 0 < e) (n : ℕ)
    (hfit : n = 0 ∨ R ≤ e) : (R / e) ^ n ≤ 1 := by
  rcases hfit with hn | hfit
  · rw [hn, pow_zero]
  · exact pow_le_one₀ (div_nonneg hR he.le) ((div_le_one he).mpr hfit)

theorem analytic_scalar_term_le {E e R A S w : ℝ} (hE : 0 < E) (he : 0 < e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hS : 0 ≤ S) (hw : 0 ≤ w) (n r : ℕ)
    (hfit : n = 0 ∨ R ≤ e) :
    E ^ r * (w * (A * S) * (R / e) ^ n / E ^ r) ≤ A * (w * S) := by
  have heq : E ^ r * (w * (A * S) * (R / e) ^ n / E ^ r) =
      (A * (w * S)) * (R / e) ^ n := by
    field_simp
  rw [heq]
  exact mul_le_of_le_one_right (mul_nonneg hA (mul_nonneg hw hS))
    (length_ratio_pow_le_one hR he n hfit)

/-- The birth-length gain, the two molecular radius gains and the factorial weights all
have the correct direction. The external slow derivative contributes only E^(-j). -/
theorem molecular_scalar_term_le {E e R ρ ν A S w : ℝ}
    (hE : 0 < E) (he : 0 < e) (hρ : 0 < ρ) (hν : 0 < ν)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hS : 0 ≤ S) (hw : 0 ≤ w)
    (hρe : ρ ≤ e) (heE : e ≤ E) (n r q j : ℕ) (hfit : n = 0 ∨ R ≤ ρ) :
    (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      (((ν * e ^ n) * w) * (A * S) * (R / e) ^ n / E ^ (r + j)) /
        (ν * ρ ^ n) ≤ A * (w * S) / E ^ j := by
  have heq :
      (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
        (((ν * e ^ n) * w) * (A * S) * (R / e) ^ n / E ^ (r + j)) /
          (ν * ρ ^ n) =
      (A * (w * S) / E ^ j) *
        ((R / ρ) ^ n * (ρ / E) ^ r * (ρ / e) ^ q /
          ((r.factorial : ℝ) * (q.factorial : ℝ))) := by
    simp only [div_pow, pow_add]
    field_simp
  rw [heq]
  have hnr := length_ratio_pow_le_one hR hρ n hfit
  have hrr := length_ratio_pow_le_one hρ.le hE r (Or.inr (hρe.trans heE))
  have hqr := length_ratio_pow_le_one hρ.le he q (Or.inr hρe)
  have hprod : (R / ρ) ^ n * (ρ / E) ^ r * (ρ / e) ^ q ≤ 1 :=
    (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hnr (pow_nonneg (div_nonneg hρ.le hE.le) _)).trans
        (by simpa only [one_mul] using hrr))
      (pow_nonneg (div_nonneg hρ.le he.le) _)).trans (by simpa only [one_mul] using hqr)
  have hfac : (1 : ℝ) ≤ (r.factorial : ℝ) * (q.factorial : ℝ) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos r)
      (by exact_mod_cast Nat.factorial_pos q)
  have hratio : (R / ρ) ^ n * (ρ / E) ^ r * (ρ / e) ^ q /
      ((r.factorial : ℝ) * (q.factorial : ℝ)) ≤ 1 :=
    (div_le_one (lt_of_lt_of_le zero_lt_one hfac)).mpr (hprod.trans hfac)
  exact mul_le_of_le_one_right
    (div_nonneg (mul_nonneg hA (mul_nonneg hw hS)) (pow_nonneg hE.le _)) hratio

theorem factorial_price_le (k cap d orderCap : ℕ) (hk : k ≤ cap) (hd : d ≤ orderCap) :
    ((k + d - 2).factorial : ℝ) / (k.factorial : ℝ) ≤
      ((cap + orderCap).factorial : ℝ) := by
  have hden : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  exact (div_le_self (Nat.cast_nonneg _) hden).trans
    (by exact_mod_cast Nat.factorial_le (by omega : k + d - 2 ≤ cap + orderCap))

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Radius normalization and finite original-order sums from all-context Cauchy jets.
This is algebra and supremum comparison; the holomorphic carrier estimate is not assumed proved. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

private theorem rectangular_sum_le (r q R Q : ℕ) (hr : r ≤ R) (hq : q ≤ Q)
    (B : ℝ≥0∞) (f : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ a ∈ Finset.range (r + 1), ∀ b ∈ Finset.range (q + 1), f a b ≤ B) :
    (∑ a ∈ Finset.range (r + 1), ∑ b ∈ Finset.range (q + 1), f a b) ≤
      (((R + 1) * (Q + 1) : ℕ) : ℝ≥0∞) * B := by
  calc
    _ ≤ ∑ _a ∈ Finset.range (r + 1), ∑ _b ∈ Finset.range (q + 1), B :=
      Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hf a ha b hb
    _ ≤ ∑ _a ∈ Finset.range (R + 1), ∑ _b ∈ Finset.range (Q + 1), B := by
      apply le_trans (Finset.sum_le_sum fun _ _ =>
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega : q + 1 ≤ Q + 1)))
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ}

/-- Close the scalar summation leaf, with costs depending on Dstar and the requested jets,
not on the ambient cap Dm or the number of components. -/
theorem molecular_radius_summation : MolecularRadiusSummationStatement := by
  classical
  intro p A hA hr _ _ D Dm j₀ b G k mres ρ hinput hCa hCm W hraw w hw
  let E := D.eps (G.level - 1)
  let e := D.eps G.level
  let ν := D.kap G.level
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos (by have := hinput.large; omega)
  have he : 0 < e := Construction.Stream.ocEpsilon_pos (by have := hinput.large; omega)
  have hν : 0 < ν := hinput.kap_pos
  have hρ : 0 < ρ := hinput.radius_pos
  have hρe : ρ ≤ e := hinput.radius_le
  have heE : e ≤ E := hinput.wavelength_le
  have hweight v u : 0 < w v / w u := div_pos (hw v) (hw u)
  have hfit (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
      (hd : d ≤ (G.fam.identity v u γ).maxOrder) :
      d - 2 = 0 ∨ (G.fam.identity v u γ).record.length ≤ ρ := by
    by_cases hn : d - 2 = 0
    · exact Or.inl hn
    · exact Or.inr (hinput.higher_length v u γ (by omega))
  have hs v u (γ : G.fam.Γ v u) : 0 ≤ (G.fam.identity v u γ).record.size :=
    (G.fam.identity v u γ).record.size_nonneg
  have hR v u (γ : G.fam.Γ v u) : 0 ≤ (G.fam.identity v u γ).record.length :=
    (G.fam.identity v u γ).record.length_pos.le
  have han (pointwise : Bool) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ℕ) (hd0 : 2 ≤ d) (hd : d ≤ (G.fam.identity v u γ).maxOrder)
      (I : DerivativeWord2 (d - 1)) (r q : ℕ) (hr : r ≤ k.Kan) (hq : q ≤ k.Lan) :
      ENNReal.ofReal (E ^ r) *
        envelopeJetSup pointwise (fun x : G.fam.Index => G.innerDomain W mres x.1 x.2) r q
          (fun x => (markerConj w G.fam).slowFlux E x.1 x.2 v u γ d I) ≤
        ENNReal.ofReal (A * (w v / w u * (G.fam.identity v u γ).record.size)) := by
    have hj := hraw.jet v u γ d hd0 hd I r q
      (hr.trans (Nat.le_max_left _ _)) (hq.trans (Nat.le_max_left _ _)) (w v / w u)
    rw [abs_of_pos (hweight v u)] at hj
    have hh := (envelopeJetSup_le_pointwise
      (fun x : G.fam.Index => G.innerDomain W mres x.1 x.2) r q
      (fun (x : G.fam.Index) t Y z => (w v / w u) • G.fam.slowFlux E x.1 x.2 v u γ d I t Y z) pointwise).trans hj
    calc
      _ ≤ ENNReal.ofReal (E ^ r) * ENNReal.ofReal
          ((w v / w u) * (A * (G.fam.identity v u γ).record.size) *
            ((G.fam.identity v u γ).record.length / e) ^ (d - 2) / E ^ r) :=
        mul_le_mul' le_rfl hh
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hE.le _)]
        exact ENNReal.ofReal_le_ofReal (analytic_scalar_term_le hE he (hR v u γ) hA
          (hs v u γ) (hweight v u).le (d - 2) r ((hfit v u γ d hd).imp_right
            fun h => h.trans hρe))
  have hmol (pointwise : Bool) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (K : ℕ) (hK : K ≤ k.Ks) (j : ℕ) (hj : j ≤ k.Jm)
      (d : ℕ) (hd0 : 2 ≤ d) (hd : d ≤ (G.fam.identity v u γ).maxOrder)
      (I : DerivativeWord2 (d - 1)) :
      (if pointwise then pointwiseMolecularJet ρ e K j
          (fun x : G.fam.Index => G.innerDomain W mres x.1 x.2)
          (fun x => (markerConj w G.fam).dimFlux ν e E x.1 x.2 v u γ d I)
        else molecularJet ρ e K j
          (fun x : G.fam.Index => G.innerDomain W mres x.1 x.2)
          (fun x => (markerConj w G.fam).dimFlux ν e E x.1 x.2 v u γ d I)) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K + d - 2).factorial : ℝ) / (K.factorial : ℝ)) ≤
      ENNReal.ofReal ((((p.Ks + 1) ^ 2 : ℕ) : ℝ) *
        ((p.Ks + p.Dstar).factorial : ℝ) * A *
        (w v / w u * (G.fam.identity v u γ).record.size) / E ^ j) := by
    let F := fun x : G.fam.Index => (markerConj w G.fam).dimFlux ν e E x.1 x.2 v u γ d I
    let dom := fun x : G.fam.Index => G.innerDomain W mres x.1 x.2
    have hdim : F = fun x t Y z => ((ν * e ^ (d - 2)) * (w v / w u)) •
        G.fam.slowFlux E x.1 x.2 v u γ d I t Y z := by
      funext x t Y z
      exact smul_smul (ν * e ^ (d - 2)) (w v / w u) _
    have hden : 0 < ν * ρ ^ (d - 2) := mul_pos hν (pow_pos hρ _)
    have hJ : (if pointwise then pointwiseMolecularJet ρ e K j dom F
        else molecularJet ρ e K j dom F) * (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ ≤
        (((p.Ks + 1) ^ 2 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (A * (w v / w u * (G.fam.identity v u γ).record.size) / E ^ j) := by
      have hexpand : (if pointwise then pointwiseMolecularJet ρ e K j dom F
          else molecularJet ρ e K j dom F) =
          ∑ r ∈ Finset.range (K + 1), ∑ q ∈ Finset.range (K + 1 - r),
            ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
              envelopeJetSup pointwise dom (r + j) q F := by
        cases pointwise <;> rfl
      rw [hexpand]
      simp_rw [Finset.sum_mul]
      apply triangular_jet_sum_le K p.Ks (hK.trans hinput.slot_order)
      intro r hr q hq
      have hrK : r ≤ K := by have := Finset.mem_range.mp hr; omega
      have hqK : q ≤ K := by have := Finset.mem_range.mp hq; omega
      have ht := hraw.jet v u γ d hd0 hd I (r + j) q
        ((Nat.add_le_add (hrK.trans hK) hj).trans (Nat.le_max_right _ _))
        ((hqK.trans hK).trans (Nat.le_max_right _ _)) ((ν * e ^ (d - 2)) * (w v / w u))
      rw [abs_of_pos (mul_pos (mul_pos hν (pow_pos he _)) (hweight v u))] at ht
      have hh : envelopeJetSup pointwise dom (r + j) q F ≤
          ENNReal.ofReal ((((ν * e ^ (d - 2)) * (w v / w u)) *
            (A * (G.fam.identity v u γ).record.size) *
            ((G.fam.identity v u γ).record.length / e) ^ (d - 2) / E ^ (r + j))) :=
        (envelopeJetSup_le_pointwise dom (r + j) q F pointwise).trans
          (by rw [hdim]; exact ht)
      have hcoef : 0 ≤ ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q) := by
        positivity
      calc
        _ ≤ (ENNReal.ofReal (ρ ^ (r + q) /
            ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
            ENNReal.ofReal ((((ν * e ^ (d - 2)) * (w v / w u)) *
              (A * (G.fam.identity v u γ).record.size) *
              ((G.fam.identity v u γ).record.length / e) ^ (d - 2) / E ^ (r + j)))) *
              (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ :=
          mul_le_mul' (mul_le_mul' le_rfl hh) le_rfl
        _ ≤ _ := by
          rw [← ENNReal.ofReal_mul hcoef, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hden]
          exact ENNReal.ofReal_le_ofReal (molecular_scalar_term_le hE he hρ hν (hR v u γ)
            hA (hs v u γ) (hweight v u).le hρe heE (d - 2) r q j (hfit v u γ d hd))
    have hfac := ENNReal.ofReal_le_ofReal (factorial_price_le K p.Ks d p.Dstar
      (hK.trans hinput.slot_order) (hd.trans (hinput.source_order v u γ)))
    apply (mul_le_mul' hJ hfac).trans_eq
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (mul_nonneg hA (mul_nonneg (hweight v u).le (hs v u γ))) (pow_nonneg hE.le _)))]
    congr 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro pp c v u γ d I tY htY z
    exact (hraw.smooth pp c v u γ d I tY htY z).const_smul (w v / w u)
  · intro pointwise v u γ
    unfold analyticConstituentPrice
    have hh := original_order_menu p.Dstar (G.fam.identity v u γ).maxOrder
      (hinput.source_order v u γ)
      ((((p.Kan + 1) * (p.Lan + 1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (A * (w v / w u * (G.fam.identity v u γ).record.size)))
      _ (fun d hd I => rectangular_sum_le k.Kan k.Lan p.Kan p.Lan
        hinput.slow_order hinput.fast_order _ _ (fun r hr q hq =>
          han pointwise v u γ d (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2 I r q
            (by have := Finset.mem_range.mp hr; omega) (by have := Finset.mem_range.mp hq; omega)))
    apply hh.trans
    have heq : (originalWordCount p.Dstar : ℝ≥0∞) *
        ((((p.Kan + 1) * (p.Lan + 1) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (A * (w v / w u * (G.fam.identity v u γ).record.size))) =
        ENNReal.ofReal (analyticCost p A * (w v / w u * (G.fam.identity v u γ).record.size)) := by
      rw [← ENNReal.ofReal_natCast (originalWordCount _),
        ← ENNReal.ofReal_natCast ((p.Kan + 1) * (p.Lan + 1)),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      simp only [analyticCost, Nat.cast_mul]
      ring
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCa
      (mul_nonneg (hweight v u).le (hs v u γ)))
  · intro K hK pointwise v u γ j hj
    unfold molecularConstituentPrice
    have hh := original_order_menu p.Dstar (G.fam.identity v u γ).maxOrder
      (hinput.source_order v u γ)
      (ENNReal.ofReal ((((p.Ks + 1) ^ 2 : ℕ) : ℝ) * ((p.Ks + p.Dstar).factorial : ℝ) * A *
        (w v / w u * (G.fam.identity v u γ).record.size) / E ^ j))
      _ (fun d hd I => hmol pointwise v u γ (K v) (hK v) j hj d
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2 I)
    apply hh.trans
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have heq : (originalWordCount p.Dstar : ℝ) *
        (((((p.Ks + 1) ^ 2 : ℕ) : ℝ) * ((p.Ks + p.Dstar).factorial : ℝ) * A *
          (w v / w u * (G.fam.identity v u γ).record.size)) / E ^ j) =
        molecularCost p A * (E ^ j)⁻¹ * (w v / w u * (G.fam.identity v u γ).record.size) := by
      simp only [molecularCost, Nat.cast_mul]
      ring
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCm j) (inv_nonneg.mpr (pow_nonneg hE.le _)))
      (mul_nonneg (hweight v u).le (hs v u γ)))

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! The shared envelope input supplies the actual chain environment
(holomorphic extension of the slow dependence). Carrier constants
are existential and are chosen before the actual chain, as in both entry prefixes. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ} {G : GenStage D hr Dm b j₀}
  {k : InvConsts} {mres ρ : ℝ} {p : ContextEnvelopeParameters}

/-- The OC stream supplies holomorphic velocities; the remaining environment is exactly the
small bandwidth and carrier-start input, without a band-chain or stage-invariant assumption. -/
theorem context_carrier_environment (h : ContextEnvelopeInput p G k mres ρ) :
    ∃ CH Υ : ℝ, CarrierOK 100 CH Υ ∧ ChainEnv D b CH Υ j₀ := by
  obtain ⟨CH, Υ, hC, hcs⟩ := h.carrier_environment
  have hvel := velC_spec p.alpha_pos p.alpha_lt p.s_pos p.s_lt p.admissible_q
    p.base_large p.profile h.stream
  refine ⟨CH, Υ, hC, ?_⟩
  exact
    { hq := h.q_pos
      hΛ := h.large
      hα := by rw [h.alpha_eq]; exact p.alpha_lt
      hζ := by rw [h.profile_eq]; exact p.profile
      hvel := fun m => by
        simpa only [OCData.eps, h.alpha_eq, h.q_eq, h.base_eq, h.profile_eq] using (hvel m).1
      hag := fun m t x => by
        simpa only [h.alpha_eq, h.q_eq, h.base_eq, h.profile_eq] using (hvel m).2 t x
      hb0 := by rw [h.bw_eq]; exact p.bw_pos
      hb1 := by rw [h.bw_eq]; exact p.bw_small
      hCH := hC.1
      hΥ := (by norm_num : (1 : ℝ) ≤ 100).trans ((le_max_left _ _).trans hC.2)
      hcs := hcs }

/-- Both prefixes choose their carrier constants existentially. Increasing the
chain constant gives CarrierOK 100 and preserves any earlier carrier-start request. -/
theorem common_carrier_constants {α q : ℝ} {Λ : ℕ} {b CH Υ : ℝ}
    (hΛ : 128 ≤ Λ) (hCH : 1 ≤ CH) (hΥ : 0 < Υ) :
    ∃ Υ' : ℝ, CarrierOK 100 CH Υ' ∧
      ∀ j₀, IsCarrierStart α q Λ b CH Υ' j₀ → IsCarrierStart α q Λ b CH Υ j₀ := by
  refine ⟨max Υ (max 100 (4 * (8 * Real.pi ^ 2))), ⟨hCH, le_max_right _ _⟩, ?_⟩
  intro j₀ hcs
  exact IsCarrierStart.mono
    (fun _ => Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)).le _)
    (fun _ => (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)).le)
    le_rfl (le_max_left _ _) (zero_le_one.trans hCH) hΥ.le hcs

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! The final-phase Fourier estimate on arbitrary complex carrier parameters. This is the
all-history version of Buffer.NativeComplexPhaseJets; periodicity is supplied directly. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Construction.Preservation.Buffer AVRegularity.Providers.ComplexFlow

/-- A literal context certificate bounds every real transverse derivative, including at
complex slow/child parameters. No native-chain or zero-child restriction is used. -/
theorem carrier_phase_regular_and_jet_bound
    {D : OCData} {b : ℝ} (hb : 0 < b) {j₀ i : ℕ} (p : OddSlot)
    {f : GenSort.Sem .ctx}
    (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D b j₀ i p.1 f (F p))
    {dd : ChainData} {n : ℕ}
    (hdd : ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p.1 ch ∧
      ch.data = dd ∧ ch.children.length = n)
    {t mres : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p.1)
    (hm2 : mres ≤ 2) (L : ℕ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ)
    (x : ChainParamsC n) (hx : x ∈ carrierC D b dd n mres)
    (hreal : ∀ a, (x.2.2 a).im = 0) (q : ℕ) :
    ContDiff ℝ (q : ℕ∞) (fun s : ℝ => F p dd n t
      (x.1, x.2.1, x.2.2 + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) ∧
    ∀ j ≤ q, ∀ s : ℝ, ‖iteratedDeriv j (fun s : ℝ => F p dd n t
      (x.1, x.2.1, x.2.2 + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) s‖ ≤
      ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ := by
  have hslot : dd.slots.getLastD 0 = p.1 := by
    obtain ⟨ch, hch, rfl, _⟩ := hdd
    exact hch.2.2.2.1
  let g : ℝ → ChainParamsC n := fun s =>
    (x.1, x.2.1, x.2.2 + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)
  have hg : Continuous g := by
    refine continuous_const.prodMk (continuous_const.prodMk (continuous_const.add ?_))
    apply continuous_pi
    intro a
    by_cases ha : a = transverseIndex p.1
    · simpa only [ite_eq_left ha] using Complex.continuous_ofReal
    · simp only [ite_eq_right ha]
      exact continuous_const
  have hgm (s : ℝ) : g s ∈ carrierC D b dd n mres := by
    refine ⟨hx.1, hx.2.1, ?_⟩
    simpa only [g, Complex.add_im, Pi.add_apply, hslot, ite_true, Complex.ofReal_im,
      add_zero] using hx.2.2
  have hgm2 (s : ℝ) : g s ∈ carrierC D b dd n 2 := carrierC_mono hb.le hm2 (hgm s)
  have hc : Continuous (fun s => F p dd n t (g s)) :=
    continuousOn_univ.mp ((hF.1 dd n t ht).continuousOn.comp hg.continuousOn
      (fun s _ => hgm2 s))
  have hp : Function.Periodic (fun s => F p dd n t (g s)) 1 := by
    intro s
    let v : Vec 2 := fun a => if a = transverseIndex p.1 then 1 else 0
    have hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getLastD 0)) = m := by
      refine ⟨1, ?_⟩
      simp only [v, hslot, ite_true, Int.cast_one]
    have he : g (s + 1) = (g s).shiftFinal v := by
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext a
      by_cases ha : a = transverseIndex p.1
      · simp only [g, ChainParamsC.shiftFinal, v, ha, ite_true, Pi.add_apply,
          Complex.ofReal_add, Complex.ofReal_one, add_assoc]
      · simp only [g, ChainParamsC.shiftFinal, v, ha, ite_false, Pi.add_apply,
          Complex.ofReal_zero, add_zero]
    change F p dd n t (g (s + 1)) = F p dd n t (g s)
    rw [he]
    exact (hF.2.1.2.1 dd n t ht (g s) (hgm2 s)).1 v hv
  have hcoeff (h : ℤ) :
      ‖CycleComparison.Lift.unitProfileFourierCoeff (fun s => F p dd n t (g s)) h‖ₑ ≤
        ctxModeSup D b j₀ i p.1 (F p) mres h := by
    rw [show CycleComparison.Lift.unitProfileFourierCoeff (fun s => F p dd n t (g s)) h =
      finalPhaseCoeff (transverseIndex p.1) (F p dd n t) x h from
        (finalPhaseCoeff_eq_fourierCoeffOn (transverseIndex p.1) (F p dd n t) x h).symm]
    exact finalPhaseCoeff_enorm_le_ctxModeSup D b j₀ i p.1 (F p) mres h dd n hdd t ht x hx hreal
  exact context_profile_regular_and_jet_bound D b hb j₀ i F mres L p _ hc hp hcoeff θ hθ hsize q

/-- The same certificate bounds the genuine two-dimensional fast jets, uniformly in all
real final phases. Parallel phase invariance is part of the periodicity statement, not an extra
stage hypothesis. -/
theorem carrier_fast_regular_and_jet_bound
    {D : OCData} {b : ℝ} (hb : 0 < b) {j₀ i : ℕ} (p : OddSlot)
    {f : GenSort.Sem .ctx}
    (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D b j₀ i p.1 f (F p))
    {dd : ChainData} {n : ℕ}
    (hdd : ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p.1 ch ∧
      ch.data = dd ∧ ch.children.length = n)
    {t mres : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p.1)
    (hm2 : mres ≤ 2) (L : ℕ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsize : ctxSize D b j₀ i F mres L ≤ ENNReal.ofReal θ)
    (x : ChainParamsC n) (hx : x ∈ carrierC D b dd n mres)
    (hreal : ∀ a, (x.2.2 a).im = 0) (q : ℕ) :
    ContDiff ℝ (q : ℕ∞) (fun z : Vec 2 => F p dd n t (x.1, x.2.1, ofRealVec z)) ∧
    ∀ j ≤ q, ∀ z : Vec 2, ‖iteratedFDeriv ℝ j
      (fun z : Vec 2 => F p dd n t (x.1, x.2.1, ofRealVec z)) z‖ ≤
      ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ := by
  have hslot : dd.slots.getLastD 0 = p.1 := by
    obtain ⟨ch, hch, rfl, _⟩ := hdd
    exact hch.2.2.2.1
  let g : Vec 2 → ℂ := fun z => F p dd n t (x.1, x.2.1, ofRealVec z)
  have hzmem (z : Vec 2) : (x.1, x.2.1, ofRealVec z) ∈ carrierC D b dd n mres := by
    refine ⟨hx.1, hx.2.1, ?_⟩
    simpa only [ofRealVec, Complex.ofReal_im, hreal, abs_zero] using hx.2.2
  have hne : transverseIndex p.1 ≠ slotParallel p.1 := by
    rw [transverseIndex_eq_slotParallel_rev]
    generalize slotParallel p.1 = a
    fin_cases a <;> decide
  have hpar (z : Vec 2) (s : ℝ) : g (z + s • basisVec (slotParallel p.1)) = g z := by
    have hv : ∃ m : ℤ, (s • basisVec (slotParallel p.1))
        (transverseIndex (dd.slots.getLastD 0)) = m := by
      refine ⟨0, ?_⟩
      simp only [hslot, Pi.smul_apply, smul_eq_mul, basisVec_apply, hne, ite_false,
        mul_zero, Int.cast_zero]
    have hh := (hF.2.1.2.1 dd n t ht _ (carrierC_mono hb.le hm2 (hzmem z))).1
      (s • basisVec (slotParallel p.1)) hv
    have he : ofRealVec (z + s • basisVec (slotParallel p.1)) =
        ofRealVec z + (fun a => ((s • basisVec (slotParallel p.1)) a : ℂ)) := by
      ext a
      simp only [ofRealVec, Pi.add_apply, Complex.ofReal_add]
    change F p dd n t (x.1, x.2.1, _) = _
    rw [he]
    exact hh
  have hshift (z : Vec 2) :
      ContDiff ℝ (q : ℕ∞) (fun X : Vec 2 => g (z + X)) ∧
      ∀ j ≤ q, ∀ X : Vec 2, ‖iteratedFDeriv ℝ j (fun X : Vec 2 => g (z + X)) X‖ ≤
        ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ := by
    have hp := carrier_phase_regular_and_jet_bound hb p F hF hdd ht hm2 L hθ hsize
      (x.1, x.2.1, ofRealVec z) (hzmem z) (fun _ => Complex.ofReal_im _) q
    have he : (fun s : ℝ => g (z + s • basisVec (slotParallel p.1).rev)) =
        (fun s : ℝ => F p dd n t (x.1, x.2.1,
          ofRealVec z + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) := by
      funext s
      rw [← transverseIndex_eq_slotParallel_rev]
      exact congrArg (fun y => F p dd n t (x.1, x.2.1, y))
        (complex_real_phase_shift z (transverseIndex p.1) s)
    have hs := fast_affine_profile_regular_and_jet_bound (slotParallel p.1) g hpar z 1 q
      (he.symm ▸ hp.1) (fun j => ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ)
      (by simpa only [he] using hp.2)
    have hproj : ‖(ContinuousLinearMap.proj (slotParallel p.1).rev : Vec 2 →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun X => by
        simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm X _)
    refine ⟨by simpa only [one_smul] using hs.1, ?_⟩
    intro j hj X
    have hbound : ‖iteratedFDeriv ℝ j (fun X : Vec 2 => g (z + X)) X‖ ≤
        (((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ) *
          ‖(ContinuousLinearMap.proj (slotParallel p.1).rev : Vec 2 →L[ℝ] ℝ)‖ ^ j := by
      simpa only [one_smul] using hs.2 j hj X
    apply hbound.trans
    have hcost : 0 ≤ ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ j) * θ := by positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (n := j) (norm_nonneg _) hproj) hcost
  refine ⟨by simpa only [zero_add] using (hshift 0).1, ?_⟩
  intro j hj z
  simpa only [iteratedFDeriv_comp_add_left, add_zero] using (hshift z).2 j hj 0

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end
end

section
section
/-! Reuse the scalar two-coordinate Cauchy estimate for Banach-valued fast-jet maps.
The constants are chosen before the codomain, so in particular before every fast-jet space. -/
@[expose] public noncomputable section
open Homogenization Complex Metric Set
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Construction.Preservation.Buffer AVRegularity.Providers.ComplexFlow

/-- A bounded holomorphic map on a complex two-coordinate ball has uniform real jets at
its center. Hahn--Banach transfers the existing scalar contour estimate to any codomain. -/
theorem holomorphic_ball_exists_real_jet_bounds (R : ℝ) (hR : 0 < R) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (F : (Fin 2 → ℂ) → E), ContDiffOn ℂ (⊤ : ℕ∞) F (ball 0 R) →
      ∀ M : ℝ, 0 ≤ M → (∀ Z ∈ ball 0 R, ‖F Z‖ ≤ M) →
      ContDiffAt ℝ (n : ℕ∞) (fun X : Vec 2 => F (ofRealVec X)) 0 ∧
      ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun X : Vec 2 => F (ofRealVec X)) 0‖ ≤ B j * M := by
  obtain ⟨B, hB, hCauchy⟩ := two_coordinate_cauchy_exists_real_jet_bounds
    (R / 2) (by positivity) n
  refine ⟨B, hB, ?_⟩
  intro E _ _ _ F hF M hM hb
  let realF : Vec 2 → E := fun X => F (ofRealVec X)
  have hzero : (ofRealVec (0 : Vec 2)) ∈ ball (0 : Fin 2 → ℂ) R := by
    change ofRealVecCLM 0 ∈ ball (0 : Fin 2 → ℂ) R
    rw [map_zero]
    exact mem_ball_self hR
  have hs : ContDiffAt ℝ (n : ℕ∞) realF 0 := by
    have hh := hF.contDiffAt (isOpen_ball.mem_nhds hzero)
    exact (hh.restrict_scalars ℝ).comp 0 ofRealVecCLM.contDiff.contDiffAt |>.of_le (by simp)
  refine ⟨hs, ?_⟩
  intro j hj
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (hB j) hM)
  intro v
  apply NormedSpace.norm_le_dual_bound ℂ _ (mul_nonneg (mul_nonneg (hB j) hM) (Finset.prod_nonneg
    (fun a _ => norm_nonneg (v a))))
  intro L
  let coord : ℂ → ℂ → Fin 2 → ℂ := fun w z a => if a = 0 then w else z
  have hcoord (w z : ℂ) (hw : w ∈ closedBall 0 (R / 2))
      (hz : z ∈ closedBall 0 (R / 2)) : coord w z ∈ ball (0 : Fin 2 → ℂ) R := by
    apply mem_ball_zero_iff.mpr
    apply lt_of_le_of_lt (b := R / 2) _ (by linarith only [hR])
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    dsimp only [coord]
    split_ifs
    · simpa only [mem_closedBall, dist_zero_right] using hw
    · simpa only [mem_closedBall, dist_zero_right] using hz
  have hwd (z : ℂ) : Differentiable ℂ (fun w => coord w z) := by
    apply differentiable_pi.mpr
    intro a
    by_cases ha : a = 0 <;> simp only [coord, ha, ite_true, ite_false] <;> fun_prop
  have hzd (w : ℂ) : Differentiable ℂ (coord w) := by
    apply differentiable_pi.mpr
    intro a
    by_cases ha : a = 0 <;> simp only [coord, ha, ite_true, ite_false] <;> fun_prop
  have hLF : DifferentiableOn ℂ (fun Z => L (F Z)) (ball 0 R) := L.differentiable.comp_differentiableOn (hF.differentiableOn (by simp))
  have h₀ : ∀ z ∈ closedBall 0 (R / 2),
      DiffContOnCl ℂ (fun w => L (F (coord w z))) (ball 0 (R / 2)) := by
    intro z hz
    exact DiffContOnCl.mk_ball
      (hLF.comp (hwd z).differentiableOn (fun w hw => hcoord w z (ball_subset_closedBall hw) hz))
      (hLF.continuousOn.comp (hwd z).continuous.continuousOn (fun w hw => hcoord w z hw hz))
  have h₁ : ∀ w ∈ closedBall 0 (R / 2),
      DiffContOnCl ℂ (fun z => L (F (coord w z))) (ball 0 (R / 2)) := by
    intro w hw
    exact DiffContOnCl.mk_ball
      (hLF.comp (hzd w).differentiableOn (fun z hz => hcoord w z hw (ball_subset_closedBall hz)))
      (hLF.continuousOn.comp (hzd w).continuous.continuousOn (fun z hz => hcoord w z hw hz))
  have hcircle (θ : ℝ) : circleMap 0 (R / 2) θ ∈ closedBall 0 (R / 2) := by
    simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos (by positivity : 0 < R / 2), le_refl]
  have hc : Continuous (fun p : ℝ × ℝ =>
      L (F (coord (circleMap 0 (R / 2) p.1) (circleMap 0 (R / 2) p.2)))) := by
    have hh : Continuous (fun p : ℝ × ℝ =>
        coord (circleMap 0 (R / 2) p.1) (circleMap 0 (R / 2) p.2)) := by
      apply continuous_pi
      intro a
      by_cases ha : a = 0
      · simpa only [coord, ha, ite_true, Function.comp_def] using (continuous_circleMap 0 (R / 2)).comp continuous_fst
      · simpa only [coord, ha, ite_false, Function.comp_def] using (continuous_circleMap 0 (R / 2)).comp continuous_snd
    exact continuousOn_univ.mp (hLF.continuousOn.comp hh.continuousOn
      (fun p _ => hcoord _ _ (hcircle p.1) (hcircle p.2)))
  obtain ⟨_, hjet⟩ := hCauchy (fun w z => L (F (coord w z))) h₀ h₁ hc
    (‖L‖ * M) (mul_nonneg (norm_nonneg _) hM)
    (fun θ φ => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (hb _ (hcoord _ _ (hcircle θ) (hcircle φ))) (norm_nonneg _)))
  have he : (fun X : Vec 2 => L (F (coord (X 0 : ℂ) (X 1 : ℂ)))) =
      (L.restrictScalars ℝ) ∘ realF := by
    funext X
    change L (F (coord (X 0 : ℂ) (X 1 : ℂ))) = L (F (ofRealVec X))
    congr 1
    congr 1
    funext a
    fin_cases a <;> rfl
  have hh := hjet j hj
  rw [he, (L.restrictScalars ℝ).iteratedFDeriv_comp_left hs (by exact_mod_cast hj)] at hh
  exact ((L.restrictScalars ℝ).compContinuousMultilinearMap
    (iteratedFDeriv ℝ j realF 0)).le_opNorm v |>.trans
      ((mul_le_mul_of_nonneg_right hh (Finset.prod_nonneg (fun a _ => norm_nonneg (v a)))).trans_eq
        (by ring))

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! The real fast jet of a jointly holomorphic scalar context remains a holomorphic
Banach-valued function of the slow coordinates. Scalar restriction is complex linear on the
codomain; no complex structure is imposed on the real fast domain. -/
@[expose] public noncomputable section
open Homogenization Set Metric
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow

/-- Insert a real fast increment into the second complex coordinate block. -/
def realFastInclusion : Vec 2 →L[ℝ] (CVec × CVec) :=
  (ContinuousLinearMap.inr ℝ CVec CVec).comp ofRealVecCLM

/-- Restrict a joint complex jet to real fast directions; this operation is complex linear
in the value of the jet, despite the real domain of the resulting multilinear map. -/
def realFastJetProjection (q : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin q => CVec × CVec) ℂ →L[ℂ]
      ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℂ where
  toFun T := (T.restrictScalars ℝ).compContinuousLinearMap (fun _ => realFastInclusion)
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl
  cont := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℂ)
    (fun _ : Fin q => realFastInclusion)).continuous.comp
      ContinuousMultilinearMap.continuous_restrictScalars

/-- Identify the genuine real fast jet with a fixed projection of the complex joint jet.
The equality is local on the holomorphic domain; no global smoothness is assumed. -/
theorem real_fast_jet_eq_projection {F : CVec × CVec → ℂ} {U : Set (CVec × CVec)}
    (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (q : ℕ) (Z : CVec) (z : Vec 2) (hx : (Z, ofRealVec z) ∈ U) :
    iteratedFDeriv ℝ q (fun x : Vec 2 => F (Z, ofRealVec x)) z =
      realFastJetProjection q (iteratedFDeriv ℂ q F (Z, ofRealVec z)) := by
  let g : CVec × CVec → ℂ := fun y => F (y + (Z, 0))
  let S : Set (CVec × CVec) := (fun y => y + (Z, 0)) ⁻¹' U
  have hS : IsOpen S := hU.preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ (q : ℕ) g S := by
    exact ((hF.restrict_scalars ℝ).comp (contDiff_id.add contDiff_const).contDiffOn
      (mapsTo_preimage _ _)).of_le (by simp)
  have hpre : IsOpen (realFastInclusion ⁻¹' S) := hS.preimage realFastInclusion.continuous
  have hz : realFastInclusion z ∈ S := by simpa only [S, realFastInclusion,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
    zero_add, add_zero, ofRealVecCLM_apply, mem_preimage] using hx
  have he : g ∘ realFastInclusion = fun x : Vec 2 => F (Z, ofRealVec x) := by
    funext x
    simp only [Function.comp_apply, g, realFastInclusion, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero, ofRealVecCLM_apply]
  have hc := realFastInclusion.iteratedFDerivWithin_comp_right hg hS.uniqueDiffOn
    hpre.uniqueDiffOn hz (i := q) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
    ((hg.comp_continuousLinearMap realFastInclusion).contDiffAt (hpre.mem_nhds hz)) hz,
    iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn
      (hg.contDiffAt (hS.mem_nhds hz)) hz, he] at hc
  rw [iteratedFDeriv_comp_add_right] at hc
  have hcx : ContDiffAt ℂ (q : ℕ) F (Z, ofRealVec z) :=
    (hF.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hrestrict := hcx.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  change iteratedFDeriv ℝ q (fun x : Vec 2 => F (Z, ofRealVec x)) z =
    ((iteratedFDeriv ℂ q F (Z, ofRealVec z)).restrictScalars ℝ).compContinuousLinearMap
      (fun _ => realFastInclusion)
  simp only [Function.comp_apply] at hrestrict
  rw [hrestrict]
  simpa only [realFastInclusion, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ofRealVecCLM_apply, Prod.mk_add_mk, zero_add, add_zero] using hc

/-- Fast differentiation preserves holomorphic dependence on the slow block. This is a
local consequence of joint holomorphy, rather than an interchange hypothesis. -/
theorem contDiffOn_real_fast_jet {F : CVec × CVec → ℂ} {U : Set (CVec × CVec)}
    (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (q : ℕ) (z : Vec 2) :
    ContDiffOn ℂ (⊤ : ℕ∞)
      (fun Z : CVec => iteratedFDeriv ℝ q (fun x : Vec 2 => F (Z, ofRealVec x)) z)
      {Z | (Z, ofRealVec z) ∈ U} := by
  have hs : ContDiffOn ℂ (⊤ : ℕ∞)
      (fun Z : CVec => realFastJetProjection q (iteratedFDeriv ℂ q F (Z, ofRealVec z)))
      {Z | (Z, ofRealVec z) ∈ U} := by
    intro Z hZ
    have hJ := (hF.contDiffAt (hU.mem_nhds hZ)).iteratedFDeriv_right
      (m := (⊤ : ℕ∞)) (i := q) (by simp)
    exact ((realFastJetProjection q).contDiff.contDiffAt.comp Z
      (hJ.comp Z (contDiff_id.prodMk contDiff_const).contDiffAt)).contDiffWithinAt
  exact hs.congr (fun Z hZ => real_fast_jet_eq_projection hU hF q Z z hZ)

/-- Uniform slow Cauchy estimates applied to the actual fast-jet map. The Cauchy constants
precede the fast order, the holomorphic context, and its time/history parameters. -/
theorem mixed_holomorphic_ball_exists_real_jet_bounds (R : ℝ) (hR : 0 < R) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
    ∀ (q : ℕ) (F : CVec × CVec → ℂ) (U : Set (CVec × CVec)), IsOpen U →
      ContDiffOn ℂ (⊤ : ℕ∞) F U →
      (∀ Z ∈ ball (0 : CVec) R, ∀ z : Vec 2, (Z, ofRealVec z) ∈ U) →
      ∀ M : ℝ, 0 ≤ M →
        (∀ Z ∈ ball (0 : CVec) R, ∀ z : Vec 2,
          ‖iteratedFDeriv ℝ q (fun x : Vec 2 => F (Z, ofRealVec x)) z‖ ≤ M) →
        ∀ z : Vec 2,
          ContDiffAt ℝ (n : ℕ∞) (fun X : Vec 2 =>
            iteratedFDeriv ℝ q (fun x : Vec 2 => F (ofRealVec X, ofRealVec x)) z) 0 ∧
          ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
            iteratedFDeriv ℝ q (fun x : Vec 2 => F (ofRealVec X, ofRealVec x)) z) 0‖ ≤ B j * M := by
  obtain ⟨B, hB, hCauchy⟩ := holomorphic_ball_exists_real_jet_bounds R hR n
  refine ⟨B, hB, ?_⟩
  intro q F U hU hF hreal M hM hb z
  have hs := (contDiffOn_real_fast_jet hU hF q z).mono (fun Z hZ => hreal Z hZ z)
  exact hCauchy (ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℂ)
    (fun Z => iteratedFDeriv ℝ q (fun x : Vec 2 => F (Z, ofRealVec x)) z)
    hs M hM (fun Z hZ => hb Z hZ z)

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! The holomorphic slow extension (`Providers.ComplexContext`) provides a genuine complex
slow neighborhood for every history. The radius is scaled by the parent wavelength; the reserve gap and bandwidth are the only fixed losses. -/
@[expose] public noncomputable section
open Homogenization Set Metric
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.ComplexContext AVRegularity.Providers.GenSem

/-- Recenter the slow parameters and replace the final phase. -/
def recenteredCarrierFunction {D : OCData} {dd : ChainData} {n : ℕ}
    (F : ChainParamsC n → ℂ) (x : ChainParamsC n) (y : CVec × CVec) : ℂ :=
  F (recC D dd n (x.1, x.2.1, y.2) y.1)

/-- The local product carrier used for mixed slow/fast jets. -/
def recenteredCarrierDomain (D : OCData) (b : ℝ) (dd : ChainData) (n : ℕ)
    (mres Δ : ℝ) : Set (CVec × CVec) :=
  ball 0 (b * D.eps (dd.baseLevel + n) * Δ / 24) ×ˢ
    {z : CVec | |(z (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b}

/-- The reserve-gap product carrier is open, including the unrestricted parallel phase. -/
theorem isOpen_recenteredCarrierDomain (D : OCData) (b : ℝ) (dd : ChainData) (n : ℕ)
    (mres Δ : ℝ) : IsOpen (recenteredCarrierDomain D b dd n mres Δ) :=
  isOpen_ball.prod (isOpen_lt
    ((Complex.continuous_im.comp (continuous_apply _)).abs) continuous_const)

/-- Uniform recentering geometry and holomorphy on the local product carrier. All histories
use exactly the radius of the slow extension; there is no depth-dependent loss. -/
theorem recentered_carrier_holomorphic
    {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} (env : ChainEnv D b CH Υ j₀)
    {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    {mres Δ : ℝ} (hm : 0 ≤ mres) (hΔ : 0 < Δ) (hmΔ : mres + Δ ≤ 2)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres)
    {F : ChainParamsC n → ℂ} (hF : DifferentiableOn ℂ F (carrierC D b dd n 2)) :
    ContDiffOn ℂ (⊤ : ℕ∞) (recenteredCarrierFunction (D := D) (dd := dd) F x)
      (recenteredCarrierDomain D b dd n mres Δ) ∧
    ∀ y ∈ recenteredCarrierDomain D b dd n mres Δ,
      recC D dd n (x.1, x.2.1, y.2) y.1 ∈ carrierC D b dd n (mres + Δ) := by
  let P : CVec × CVec → ChainParamsC n × CVec := fun y => ((x.1, x.2.1, y.2), y.1)
  have hP : Differentiable ℂ P := by
    dsimp only [P]
    fun_prop
  have hε : 0 < D.eps (dd.baseLevel + n) := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hsmall : b * D.eps (dd.baseLevel + n) * Δ / 24 < b * D.eps (dd.baseLevel + n) := by
    have hpos := mul_pos env.hb0 hε
    have hΔ2 : Δ ≤ 2 := by linarith only [hmΔ, hm]
    nlinarith only [hpos, hΔ2]
  have hx' (y : CVec × CVec) (hy : y ∈ recenteredCarrierDomain D b dd n mres Δ) :
      (x.1, x.2.1, y.2) ∈ carrierC D b dd n mres := ⟨hx.1, hx.2.1, hy.2⟩
  have hnorm (y : CVec × CVec) (hy : y ∈ recenteredCarrierDomain D b dd n mres Δ) :
      ‖y.1‖ < b * D.eps (dd.baseLevel + n) * Δ / 24 := mem_ball_zero_iff.mp hy.1
  have hmaps : MapsTo P (recenteredCarrierDomain D b dd n mres Δ)
      (carrierC D b dd n 2 ×ˢ ball 0 (b * D.eps (dd.baseLevel + n))) := by
    intro y hy
    exact ⟨carrierC_mono env.hb0.le (by linarith only [hmΔ, hΔ]) (hx' y hy),
      mem_ball_zero_iff.mpr ((hnorm y hy).trans hsmall)⟩
  have hmem (y : CVec × CVec) (hy : y ∈ recenteredCarrierDomain D b dd n mres Δ) :
      recC D dd n (x.1, x.2.1, y.2) y.1 ∈ carrierC D b dd n (mres + Δ) := by
    apply recC_mem env hdd hm hΔ hmΔ (hx' y hy)
    apply (hnorm y hy).le.trans
    have hpos := mul_nonneg (mul_nonneg env.hb0.le hε.le) hΔ.le
    linarith only [hpos]
  refine ⟨?_, hmem⟩
  apply contDiffOn_top_of_differentiableOn (isOpen_recenteredCarrierDomain D b dd n mres Δ)
  exact hF.comp ((differentiableOn_recC env hdd).comp hP.differentiableOn hmaps)
    (fun y hy => carrierC_mono env.hb0.le hmΔ (hmem y hy))

/-- Normalize the physical slow offset by its parent wavelength before taking Cauchy jets. -/
def normalizedRecenteredCarrierFunction {D : OCData} {dd : ChainData} {n : ℕ}
    (F : ChainParamsC n → ℂ) (x : ChainParamsC n) (y : CVec × CVec) : ℂ :=
  recenteredCarrierFunction (D := D) (dd := dd) F x
    (((D.eps (dd.baseLevel + n) : ℂ) • y.1), y.2)

/-- The normalized slow radius depends only on the bandwidth and reserve gap. This keeps
the eventual Cauchy constants independent of the level, history and ambient source-order cap. -/
theorem normalized_recentered_carrier_holomorphic
    {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ} (env : ChainEnv D b CH Υ j₀)
    {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    {mres Δ : ℝ} (hm : 0 ≤ mres) (hΔ : 0 < Δ) (hmΔ : mres + Δ ≤ 2)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres)
    {F : ChainParamsC n → ℂ} (hF : DifferentiableOn ℂ F (carrierC D b dd n 2)) :
    ContDiffOn ℂ (⊤ : ℕ∞) (normalizedRecenteredCarrierFunction (D := D) (dd := dd) F x)
      (ball 0 (b * Δ / 24) ×ˢ
        {z : CVec | |(z (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b}) ∧
    ∀ y ∈ (ball 0 (b * Δ / 24) ×ˢ
        {z : CVec | |(z (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b}),
      recC D dd n (x.1, x.2.1, y.2) ((D.eps (dd.baseLevel + n) : ℂ) • y.1) ∈
        carrierC D b dd n (mres + Δ) := by
  obtain ⟨hs, hmem⟩ := recentered_carrier_holomorphic env hdd hm hΔ hmΔ hx hF
  let T : CVec × CVec → CVec × CVec := fun y => (((D.eps (dd.baseLevel + n) : ℂ) • y.1), y.2)
  have hT : ContDiff ℂ (⊤ : ℕ∞) T := by dsimp only [T]; fun_prop
  have hε : 0 < D.eps (dd.baseLevel + n) := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hmaps : MapsTo T
      (ball 0 (b * Δ / 24) ×ˢ
        {z : CVec | |(z (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b})
      (recenteredCarrierDomain D b dd n mres Δ) := by
    intro y hy
    refine ⟨mem_ball_zero_iff.mpr ?_, hy.2⟩
    change ‖(D.eps (dd.baseLevel + n) : ℂ) • y.1‖ < _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hy.1) hε).trans_eq (by ring)
  exact ⟨hs.comp hT.contDiffOn hmaps, fun y hy => hmem (T y) (hmaps hy)⟩

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! The shared analytic estimate: all mixed jets on every history, with a fixed reserve
loss and a normalized slow radius. Fourier decay controls arbitrarily many fast derivatives. -/
@[expose] public noncomputable section
open Homogenization Set Metric
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.ComplexContext

/-- Constants are chosen before the level, discrete history, output time, context function
and fast-jet space. They depend only on the fixed bandwidth, reserve gap and slow menu. -/
theorem carrier_exists_normalized_mixed_jet_bounds (b Δ : ℝ) (hb : 0 < b) (hΔ : 0 < Δ)
    (N : ℕ) : ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
    ∀ (D : OCData) (CH Υ : ℝ) (j₀ i : ℕ), ChainEnv D b CH Υ j₀ →
    ∀ (p : OddSlot) (dd : ChainData) (n : ℕ), AdmData D b j₀ i p.1 dd n →
    ∀ (f : GenSort.Sem .ctx)
      (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
      IsHolExtension D b j₀ i p.1 f (F p) →
    ∀ (t mres mcert : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ i p.1 →
      0 ≤ mres → mres + Δ ≤ mcert → mcert ≤ 2 →
    ∀ (L : ℕ) (θ : ℝ), 0 ≤ θ → ctxSize D b j₀ i F mcert L ≤ ENNReal.ofReal θ →
    ∀ (x : ChainParamsC n), x ∈ carrierC D b dd n mres →
    ∀ (q : ℕ) (z : Vec 2),
      ContDiffAt ℝ (N : ℕ∞) (fun X : Vec 2 => iteratedFDeriv ℝ q
        (fun z : Vec 2 => normalizedRecenteredCarrierFunction (D := D) (dd := dd)
          (F p dd n t) x (ofRealVec X, ofRealVec z)) z) 0 ∧
      ∀ r ≤ N, ‖iteratedFDeriv ℝ r (fun X : Vec 2 => iteratedFDeriv ℝ q
        (fun z : Vec 2 => normalizedRecenteredCarrierFunction (D := D) (dd := dd)
          (F p dd n t) x (ofRealVec X, ofRealVec z)) z) 0‖ ≤
        B r * (((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * θ) := by
  obtain ⟨B, hB, hCauchy⟩ := mixed_holomorphic_ball_exists_real_jet_bounds
    (b * Δ / 24) (by positivity) N
  refine ⟨B, hB, ?_⟩
  intro D CH Υ j₀ i env p dd n hdd f F hF t mres mcert ht hm hmcert hcert L θ hθ hsize x hx q z
  let V : Set CVec := {z | |(z (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b}
  let U : Set (CVec × CVec) := ball 0 (b * Δ / 24) ×ˢ V
  let g : CVec × CVec → ℂ :=
    normalizedRecenteredCarrierFunction (D := D) (dd := dd) (F p dd n t) x
  have hgap : mres + Δ ≤ 2 := hmcert.trans hcert
  obtain ⟨hg, hmem⟩ := normalized_recentered_carrier_holomorphic env hdd.goodData.1
    hm hΔ hgap hx (hF.1 dd n t ht)
  have hV : IsOpen V := isOpen_lt
    ((Complex.continuous_im.comp (continuous_apply _)).abs) continuous_const
  have hphase (z : Vec 2) : ofRealVec z ∈ V := by
    change |((ofRealVec z) (transverseIndex (dd.slots.getLastD 0))).im| < _
    simp only [ofRealVec, Complex.ofReal_im, abs_zero]
    have hwidth : 0 < 3 + mres / 4 := by linarith only [hm]
    exact mul_pos hwidth hb
  have hreal : ∀ Z ∈ ball (0 : CVec) (b * Δ / 24), ∀ z : Vec 2, (Z, ofRealVec z) ∈ U :=
    fun Z hZ z => ⟨hZ, hphase z⟩
  have hfast (Z : CVec) (hZ : Z ∈ ball (0 : CVec) (b * Δ / 24)) (z : Vec 2) :
      ‖iteratedFDeriv ℝ q (fun z : Vec 2 => g (Z, ofRealVec z)) z‖ ≤
        ((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * θ := by
    let y : ChainParamsC n := recC D dd n (x.1, x.2.1, ofRealVec 0)
      ((D.eps (dd.baseLevel + n) : ℂ) • Z)
    have hy : y ∈ carrierC D b dd n mcert := carrierC_mono hb.le hmcert
      (hmem (Z, ofRealVec 0) ⟨hZ, hphase 0⟩)
    have hyr : ∀ a, (y.2.2 a).im = 0 := by
      intro a
      dsimp only [y]
      rw [recC_snd_snd]
      exact Complex.ofReal_im _
    have he : (fun z : Vec 2 => g (Z, ofRealVec z)) =
        (fun z : Vec 2 => F p dd n t (y.1, y.2.1, ofRealVec z)) := by
      funext z
      exact congrArg (F p dd n t)
        (recC_final D dd n (x.1, x.2.1, ofRealVec 0) (ofRealVec z)
          ((D.eps (dd.baseLevel + n) : ℂ) • Z))
    rw [he]
    exact (carrier_fast_regular_and_jet_bound hb p F hF hdd ht hcert L hθ hsize y hy hyr q).2 q le_rfl z
  exact hCauchy q g U (isOpen_ball.prod hV) hg hreal
    (((q.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * b)) ^ q) * θ)
    (by positivity) hfast z

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Realization of the local complex estimate on the actual inner real carrier. -/
@[expose] public noncomputable section
open Homogenization Set Filter
open scoped Topology
namespace AVRegularity.Construction.StageEnvelopes.Cauchy
open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.ComplexContext

/-- Raising the real carrier reserve preserves scheduling and only enlarges the center bounds. -/
theorem carrierChain_mono {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {m m' : ℝ}
    (hb : 0 ≤ b) (hmm : m ≤ m') {ch : RealChain}
    (h : IsCarrierChain D b j₀ i p m ch) : IsCarrierChain D b j₀ i p m' ch := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  intro k hk
  apply (h.2.2.2.2.2.2 k hk).trans_le
  apply mul_le_mul_of_nonneg_right _ (by
    unfold OCData.eps ocEpsilon
    split_ifs <;> positivity)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hmm]) hb)
    (by norm_num)

/-- Real points of any nonnegative inner carrier satisfy the corresponding complex bounds. -/
theorem paramsC_mem_inner_carrier {D : OCData} (hΛ : 1 ≤ D.Λ) {b : ℝ} (hb : 0 < b)
    {j₀ i : ℕ} {p : ℤ} {mres : ℝ} (hm : 0 ≤ mres) {ch : RealChain}
    (h : IsCarrierChain D b j₀ i p mres ch) (z : Vec 2) :
    ch.paramsC z ∈ carrierC D b ch.data ch.children.length mres := by
  have hε : 0 < D.eps ch.baseLevel := Construction.Stream.ocEpsilon_pos hΛ
  refine ⟨?_, (fun k => ⟨?_, ?_⟩), ?_⟩
  · simp only [RealChain.paramsC, Complex.ofReal_im, abs_zero, Finset.sum_const_zero]
    positivity
  · simpa [RealChain.paramsC, RealChain.data] using h.2.2.2.2.2.2 k.1 k.2
  · simp only [RealChain.paramsC, Complex.ofReal_im, abs_zero]
    positivity
  · simp only [RealChain.paramsC, Complex.ofReal_im, abs_zero]
    positivity

/-- The local complex recentering agrees with the real semantics on one neighborhood for
ALL final phases. This uniform neighborhood permits genuine mixed slow/fast differentiation. -/
theorem normalized_recentered_carrier_agrees
    {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ} (env : ChainEnv D b CH Υ j₀)
    {ch : RealChain} (hch : IsAdmissibleChain D b j₀ i p ch)
    {f : GenSort.Sem .ctx} {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D b j₀ i p f F) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ∀ᶠ X : Vec 2 in 𝓝 0, ∀ z : Vec 2,
      normalizedRecenteredCarrierFunction (D := D) (dd := ch.data)
        (F ch.data ch.children.length t) (ch.paramsC 0) (ofRealVec X, ofRealVec z) =
        (f t (ch.recenter D (D.eps (ch.data.baseLevel + ch.children.length) • X)) z : ℂ) := by
  let E : ℝ := D.eps (ch.data.baseLevel + ch.children.length)
  have hevent : ∀ᶠ X : Vec 2 in 𝓝 0, IsAdmissibleChain D b j₀ i p (ch.recenter D (E • X)) := by
    exact ((continuous_const.smul continuous_id).tendsto' 0 0 (smul_zero E)).eventually
      (recenter_admissible env hch)
  filter_upwards [hevent] with X hadm z
  have hl := recenter_length (D := D) ch (E • X)
  have hP := (recC_real env hch rfl z (E • X) hl).symm
  have hh := AVRegularity.Providers.GenSem.paramsC_transport (ch.recenter D (E • X)) ch.data
    ch.children.length (AVRegularity.Providers.ComplexContext.recenter_data ch (E • X)) hl _ z hP
    (fun dd n P => F dd n t P = (f t (ch.recenter D (E • X)) z : ℂ))
    (hF.2.2 _ t ht z hadm)
  have hoff : ofRealVec (E • X) = (E : ℂ) • ofRealVec X := by
    ext a
    simp only [ofRealVec, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [hoff] at hh
  change F ch.data ch.children.length t
    (recC D ch.data ch.children.length ((ch.paramsC 0).1, (ch.paramsC 0).2.1, ofRealVec z)
      ((E : ℂ) • ofRealVec X)) = _
  exact hh

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end

section
/-! Transfer the complex mixed-jet estimate to the actual real scalar semantics without
assuming real smoothness in advance. The local realization is uniform in the final phase. -/
@[expose] public noncomputable section
open Homogenization Filter
open scoped Topology
namespace AVRegularity.Construction.StageEnvelopes.Cauchy

/-- Real part on the value of a fast multilinear jet. -/
def realPartFastJet (q : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℂ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℝ :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) ℂ ℝ Complex.reCLM

/-- Taking real parts cannot enlarge a fast-jet norm. -/
theorem norm_realPartFastJet_le (q : ℕ) : ‖realPartFastJet q‖ ≤ 1 := by
  have hRe : ‖Complex.reCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z => by simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  exact (Complex.reCLM.norm_compContinuousMultilinearMap_le T).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hRe (norm_nonneg T))

/-- Realization on one slow neighborhood, for all fast phases, identifies the true mixed
jets. Complex regularity supplies every regularity hypothesis used by the transfer. -/
theorem real_mixed_jet_le_complex (r q : ℕ) (f : Vec 2 → Vec 2 → ℝ)
    (g : Vec 2 → Vec 2 → ℂ) (z : Vec 2)
    (hfast : ∀ᶠ X : Vec 2 in 𝓝 0, ContDiffAt ℝ (q : ℕ) (g X) z)
    (hslow : ContDiffAt ℝ (r : ℕ) (fun X => iteratedFDeriv ℝ q (g X) z) 0)
    (he : ∀ᶠ X : Vec 2 in 𝓝 0, ∀ z : Vec 2, g X z = (f X z : ℂ)) :
    ContDiffAt ℝ (r : ℕ) (fun X => iteratedFDeriv ℝ q (f X) z) 0 ∧
      ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (f X) z) 0‖ ≤
        ‖iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (g X) z) 0‖ := by
  have hjet : (fun X => iteratedFDeriv ℝ q (f X) z) =ᶠ[𝓝 0]
      (fun X => realPartFastJet q (iteratedFDeriv ℝ q (g X) z)) := by
    filter_upwards [hfast, he] with X hX heX
    have hf : f X = Complex.reCLM ∘ g X := by
      funext z
      change f X z = (g X z).re
      rw [heX z]
      rfl
    rw [hf, Complex.reCLM.iteratedFDeriv_comp_left hX le_rfl]
    rfl
  refine ⟨((realPartFastJet q).contDiff.contDiffAt.comp 0 hslow).congr_of_eventuallyEq hjet, ?_⟩
  rw [(hjet.iteratedFDeriv ℝ r).eq_of_nhds]
  change ‖iteratedFDeriv ℝ r ((realPartFastJet q) ∘
    (fun X => iteratedFDeriv ℝ q (g X) z)) 0‖ ≤ _
  rw [(realPartFastJet q).iteratedFDeriv_comp_left hslow le_rfl]
  exact ((realPartFastJet q).norm_compContinuousMultilinearMap_le _).trans
    (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_realPartFastJet_le q)
        (norm_nonneg (iteratedFDeriv ℝ r (fun X => iteratedFDeriv ℝ q (g X) z) 0)))

/-- Local chain rule for an iterated derivative after a fixed linear change of variables.
The standard within-domain rule suffices; no global extension is introduced. -/
theorem iteratedFDeriv_comp_clm_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (f : Vec 2 → E) (L : Vec 2 →L[ℝ] Vec 2) (x : Vec 2)
    (hf : ContDiffAt ℝ (r : ℕ) f (L x)) :
    iteratedFDeriv ℝ r (f ∘ L) x =
      (iteratedFDeriv ℝ r f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U, hU, hx, hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hfu
  have hpre := hU.preimage L.continuous
  have hh := L.iteratedFDerivWithin_comp_right hfu hU.uniqueDiffOn hpre.uniqueDiffOn hx (i := r) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
      ((hfu.comp_continuousLinearMap L).contDiffAt (hpre.mem_nhds hx)) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hf hx] at hh
  exact hh

end AVRegularity.Construction.StageEnvelopes.Cauchy
end
end
end
