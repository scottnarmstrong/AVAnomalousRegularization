-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.CycleComparison.Residual.BoundPointwise
public import AVRegularity.CycleComparison.Residual.CoarseFlux.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The exact cell means of the lifts in a quiet gap, under the additional premise
`D ≤ max (k + 1) (L + 2)` (the fast regularity of the lift sequence reaches the order `D` of the
source operator): `L_2^{(0)} = ℬ₂ I`, `L_n^{(1)} = -𝒮_n I`, all other means vanish. This is the
conditional helper `cycle_residual_quiet_mean_of_fastOrder` for the quiet means of the cycle
residual (`Providers.cycle_residual_quiet_mean`). -/

section Assemble
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ}

theorem sourceCoeff_centField {c : Prop} (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c D Φ) (j : ℕ) :
    CoefField c 0 (sourceCoeff edge η j t Φ) := by
  obtain ⟨S, hS, _, he⟩ := sourceCoeff_coefField edge hD η t hquiet hsm hΦ
  have : sourceCoeff edge η j t Φ = S j := funext fun X => funext fun z => he j X z
  rw [this]; exact hS j

theorem sourceCoeff_eq_zero_of_gt (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {j : ℕ} (hj : D < j) (X z : Vec 2) :
    sourceCoeff edge η j t (fun X' _ => a₀ X') X z = 0 := by
  have hΦ : CoefField False D (fun X' _ => a₀ X') :=
    ⟨⟨(ha.of_le (by exact_mod_cast le_top)).comp contDiff_fst, fun _ _ _ => rfl⟩, fun hf => hf.elim⟩
  obtain ⟨S, _, hz, he⟩ := sourceCoeff_coefField edge hD η t hquiet hsm hΦ
  rw [he j X z, hz j hj]

end Assemble

theorem cycle_residual_quiet_mean_of_fastOrder (N K k L D H : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (hDsZ : D ≤ max (k + 1) (L + 2)) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
      ∀ S : Set ℝ, S ⊆ Set.Icc t₀ t₁ →
        IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S →
      ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, hh ≤ H →
        ∀ n, 2 ≤ n → n ≤ N + D → ∀ t ∈ S, ∀ X,
          liftMean Q Cc (fun _ => a₀) hh n t X
            = if hh = 0 then (if n = 2 then cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 else 0)
              else if hh = 1 then -sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X 0
              else 0 := by
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq S hS hq a₀
    ha hh hhH n hn2 hnND t htS X
  have htI : t ∈ Set.Icc t₀ t₁ := hS htS
  have hD2 : 2 ≤ D := hset.D_ge
  have hN1 : 1 ≤ N := hset.N_ge
  have hsX : D ≤ K + D + 2 := by omega
  have hqs1 : 1 ≤ qs := by
    rw [hset.qs_eq]
    have : 0 < 4 * (H + 1) * (N + D) ^ 2 := by
      have : 0 < N + D := by omega
      positivity
    omega
  have hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j) := fun i j =>
    (hset.G_smooth t htI i j).of_le (by exact_mod_cast hqs1)
  have hcq : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z' :=
    fun v u d γ hγ α X z z' => hq.2 v u d γ hγ α t htS X z z'
  have hsm : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    ((hset.coeff_smooth v u d γ hγ α t htI).contDiff_slow z).of_le (by exact_mod_cast hqs1)
  have hdrift : ∀ z k, Real.sqrt Q.η * Q.v t z k = 0 := fun z k => by
    have := congrFun (hq.1 t htS z) k
    simpa using this
  have hgood : ∀ hh' ≤ H, ∀ m, GoodField 2 (liftApply m (Cc hh' m) (fun _ => a₀) t) :=
    fun hh' hh'H m => liftApply_goodField_of_seq Q hseq (r := 2) (by omega) (by omega) hh'H m ha htI
  have hcent : ∀ hh' ≤ H, ∀ m, (1 ≤ m ∨ 1 ≤ hh') →
      CoefField True D (liftApply m (Cc hh' m) (fun _ => a₀) t) := fun hh' hh'H m hm =>
    liftApply_centField_of_seq Q hseq hsX hDsZ hh'H hm ha htI
  have hbase : liftApply 0 (Cc 0 0) (fun _ => a₀) t = fun X' _ => a₀ X' := by
    funext X' z; exact hseq.1 a₀ ha t htI X' z
  have hfi0 : FastIndep (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') := fun _ _ _ => rfl
  -- the three pieces
  have hB1 := cellB1_centField Q.η Q.G Q.v t hG hdrift (hgood hh hhH (n - 1))
  have claim2 : Continuous (fun z => cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) ∧
      fieldCellMean (fun z => cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) =
        (if hh = 0 ∧ n = 2 then cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 else 0) := by
    by_cases hc : hh ≠ 0 ∨ 3 ≤ n
    · have hB2 := cellB2_centField Q.η Q.G t hG
        ((hcent hh hhH (n - 2) (by omega)).mono hD2)
      refine ⟨hB2.1.continuous_slice X, ?_⟩
      have hnot : ¬ (hh = 0 ∧ n = 2) := by omega
      rw [hB2.2 trivial X]
      simp [hnot]
    · have hh0 : hh = 0 := by omega
      have hn : n = 2 := by omega
      subst hh0 hn
      simp only [Nat.sub_self, hbase]
      have hfi := FastIndep.cellB2 Q.η Q.G t hfi0
      have hc : (fun z => cellB2 Q.η Q.G t (fun X' _ => a₀ X') X z) =
          fun _ => cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 := funext fun z => hfi X z 0
      rw [hc]
      exact ⟨continuous_const, by simpa using fieldCellMean_const _⟩
  have claim3 : Continuous (fun z => if hh = 0 then (0 : ∀ i, h i) else
        ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) ∧
      fieldCellMean (fun z => if hh = 0 then (0 : ∀ i, h i) else
        ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) =
        (if hh = 1 then sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X 0 else 0) := by
    by_cases hh0 : hh = 0
    · subst hh0
      simp only [ite_true]
      exact ⟨continuous_const, by simpa using fieldCellMean_zero⟩
    · simp only [hh0, ite_false]
      have hsrc : ∀ j, ∀ {Φ : Vec 2 → Vec 2 → ∀ i, h i}, CoefField True D Φ →
          CoefField True 0 (sourceCoeff Q.edge Q.η j t Φ) := fun j Φ hΦ =>
        sourceCoeff_centField Q.edge (by omega) Q.η t hcq hsm hΦ j
      by_cases hA : 2 ≤ hh ∨ D < n
      · have hall : CoefField True 0 (fun X z => ∑ j ∈ Finset.range (min D n + 1),
            sourceCoeff Q.edge Q.η j t
              (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) :=
          CoefField.sum _ fun j hj => hsrc j (hcent (hh - 1) (by omega) (n - j) (by
            have := Finset.mem_range.mp hj
            have h1 : min D n ≤ D := min_le_left _ _
            have h2 : min D n ≤ n := min_le_right _ _
            omega))
        refine ⟨hall.1.continuous_slice X, ?_⟩
        rw [hall.2 trivial X]
        by_cases hh1 : hh = 1
        · have hDn : D < n := by omega
          simp only [hh1, ite_true]
          have := sourceCoeff_eq_zero_of_gt Q.edge (by omega) Q.η t hcq hsm ha hDn X 0
          rw [this]
        · simp [hh1]
      · have hh1 : hh = 1 := by omega
        have hnD : n ≤ D := by omega
        subst hh1
        simp only [ite_true]
        have hmin : min D n = n := min_eq_right hnD
        rw [hmin]
        have hsplit : (fun z => ∑ j ∈ Finset.range (n + 1), sourceCoeff Q.edge Q.η j t
            (liftApply (n - j) (Cc (1 - 1) (n - j)) (fun _ => a₀) t) X z) = fun z =>
            (∑ j ∈ Finset.range n, sourceCoeff Q.edge Q.η j t
              (liftApply (n - j) (Cc (1 - 1) (n - j)) (fun _ => a₀) t) X z) +
            sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X z := by
          funext z
          rw [Finset.sum_range_succ]
          simp only [Nat.sub_self, Nat.sub_self, hbase]
        have hlow : CoefField True 0 (fun X z => ∑ j ∈ Finset.range n, sourceCoeff Q.edge Q.η j t
            (liftApply (n - j) (Cc (1 - 1) (n - j)) (fun _ => a₀) t) X z) :=
          CoefField.sum _ fun j hj => hsrc j (hcent (1 - 1) (by omega) (n - j) (by
            have := Finset.mem_range.mp hj
            omega))
        have hfn : FastIndep (sourceCoeff Q.edge Q.η n t (fun (X' : Vec 2) (_ : Vec 2) => a₀ X')) :=
          sourceCoeff_fastIndep Q.edge Q.η t n hcq hfi0
        have hc : (fun z => sourceCoeff Q.edge Q.η n t (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') X z) =
            fun _ => sourceCoeff Q.edge Q.η n t (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') X 0 :=
          funext fun z => hfn X z 0
        have hcont : Continuous (fun z => sourceCoeff Q.edge Q.η n t
            (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') X z) := by
          rw [hc]; exact continuous_const
        rw [hsplit]
        refine ⟨(hlow.1.continuous_slice X).add hcont, ?_⟩
        rw [fieldCellMean_add (hlow.1.continuous_slice X) hcont,
          hlow.2 trivial X, hc, fieldCellMean_const, zero_add]
  -- assemble
  have hmeanB1 : fieldCellMean (fun z => cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z) = 0 := hB1.2 trivial X
  have e : (fun z => liftA Q Cc (fun _ => a₀) hh n t X z) = fun z =>
      (cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z +
        cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) -
      (if hh = 0 then (0 : ∀ i, h i) else
        ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) := by
    funext z
    simp only [liftA, hn2, ite_true]
  have hmain : liftMean Q Cc (fun _ => a₀) hh n t X =
      fieldCellMean (fun z => liftA Q Cc (fun _ => a₀) hh n t X z) := rfl
  have hc1 : Continuous (fun z => cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z) := hB1.1.continuous_slice X
  have hc12 : Continuous (fun z => cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z +
      cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) :=
    hc1.add claim2.1
  rw [hmain, e, fieldCellMean_sub hc12 claim3.1, fieldCellMean_add hc1 claim2.1, hmeanB1,
    claim2.2, claim3.2]
  by_cases hh0 : hh = 0
  · subst hh0
    by_cases hn : n = 2 <;> simp [hn]
  · by_cases hh1 : hh = 1
    · subst hh1
      simp
    · simp [hh0, hh1]

end AVRegularity
end
end

section
/-! Facade for the mixed slow/fast jets of the cleanup chain: derivative words of two-scale
fields, the Leibniz expansion of word derivatives of a diagonal sample, mixed-jet sampling, fast
jets of the cell antidivergence, and fast jets along a cleanup chain. -/
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! Helper for `cycle_residual_bound`: the bound
holds under the additional premise that the word jets of the physical field are jointly
measurable in time and space. Without such a premise the statement is false (lower integrals are
only superadditive). -/

/-- Final scalar step of the residual bound. -/
theorem residual_bound_combine {res G En : ℝ≥0∞} {sν K₁ K₂ sB sT C' : ℝ} (hsν : 0 ≤ sν)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hsB : 0 ≤ sB) (hsT : 0 ≤ sT)
    (hres : res ≤ ENNReal.ofReal sν * ENNReal.ofReal K₁ * G + ENNReal.ofReal K₂ *
      ENNReal.ofReal sT * G)
    (hG : G ≤ ENNReal.ofReal sB * En) (hX : sν * K₁ * sB + K₂ * sT * sB ≤ C') :
    res ≤ ENNReal.ofReal C' * En := by
  refine hres.trans ?_
  calc ENNReal.ofReal sν * ENNReal.ofReal K₁ * G + ENNReal.ofReal K₂ * ENNReal.ofReal sT * G
      ≤ ENNReal.ofReal sν * ENNReal.ofReal K₁ * (ENNReal.ofReal sB * En)
        + ENNReal.ofReal K₂ * ENNReal.ofReal sT * (ENNReal.ofReal sB * En) := by gcongr
    _ = ENNReal.ofReal (sν * K₁ * sB + K₂ * sT * sB) * En := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ _ := by gcongr

/-- The real inequality closing the residual bound. -/
theorem residual_bound_real {a b Sp M0 Θh εN Z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hSp : Sp = M0 * Θh)
    (hSp0 : 0 ≤ Sp) (hεN : 0 ≤ εN) (hZ : 0 ≤ Z) :
    εN * a * Sp + εN * Z * b * Sp ≤ (a + b) * M0 * Θh * εN * (1 + Z) := by
  have hdiff : (a + b) * M0 * Θh * εN * (1 + Z) =
      εN * a * Sp + εN * Z * b * Sp + εN * Sp * (b + a * Z) := by rw [hSp]; ring
  rw [hdiff]
  have : 0 ≤ εN * Sp * (b + a * Z) := by positivity
  linarith

theorem cycle_residual_bound_of_measurable (Acl N D H kl Ll : ℕ) (hA : 1 ≤ Acl)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CL : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
        (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N s0 kl Ll qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + D + 2) (max (kl + 1) (Ll + 2)) t₀ t₁ N H Cc →
        ∀ (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (hh : ℕ), hh ≤ H →
          (∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
            IsLiftTailPresentation Q Cc (s0 + D + 2) (max (kl + 1) (Ll + 2)) π t₀ t₁ N s0 CL Θ hh n (f n) (F n)) →
        ∀ a : ℝ → Vec 2 → ∀ i, h i,
          (∀ t, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (a t)) → (∀ t, AVenhance.IsZ2Periodic (a t)) →
          (∀ j, j ≤ kres + 1 → ∀ (w : DerivativeWord2 j) (v : ι), Measurable
            (fun p : ℝ × Vec 2 => ‖orderedDerivative w (fun x => a p.1 x v) p.2‖ₑ)) →
        ∀ Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain s0 (max (kl + 1) (Ll + 2)) Acl (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
              (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) (fun j => Vc j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x k)
              (fun t x => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x)
            ≤ ENNReal.ofReal (C * Θ ^ hh * εc ^ N * (1 + Z)) *
              classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres a := by
  refine ⟨(Real.sqrt (8 * (Acl : ℝ) ^ 2 * tailSumConst N D (Acl + 2)) +
    Real.sqrt (16 * tailSumConst N D (Acl + 3))) * max CL 0, by positivity, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ kres s0 hkres hs0 hset
    hMe Cc hseq f F hh hhH htail a ha hper hmeas Vc hVc Z hZ
  subst hs0
  -- the empty family
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
  · simp [residualNorm, Finset.univ_eq_empty]
  -- scalars
  have he := hset.e_pos
  have hν := hset.ν_pos
  have hB := hset.B_pos
  have hρ := hset.ρ_pos
  have hsν := Real.sqrt_pos.2 hν
  have hsB := Real.sqrt_pos.2 hB
  have hℓ : 0 < ℓ := by rw [hset.ℓ_eq]; exact div_pos he hsν
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have he_eq : e = ℓ * Real.sqrt ν := by rw [hset.ℓ_eq]; field_simp
  have hεc_eq : εc = ℓ * Real.sqrt B / ρ := by rw [hset.εc_eq, hset.dstar_eq]
  have hεc0 : 0 ≤ εc := by rw [hεc_eq]; positivity
  have hνB : ν ≤ B := by
    have := hset.η_le; rw [hset.η_eq, div_le_one hB] at this; exact this
  have heρ : e ≤ ρ := by
    have h1 : εc * ρ = ℓ * Real.sqrt B := by rw [hεc_eq]; field_simp
    have h2 : εc * ρ ≤ ρ := by nlinarith [hset.εc_le]
    calc e = ℓ * Real.sqrt ν := he_eq
      _ ≤ ℓ * Real.sqrt B := by gcongr
      _ = εc * ρ := h1.symm
      _ ≤ ρ := h2
  have hΘ : 0 ≤ Θ := le_trans (Finset.sum_nonneg fun u _ => hset.envelope.nonneg v₀ u)
    (hset.envelope.row_sum v₀)
  obtain ⟨Mn, hMn⟩ := hMe
  set S := CL * Θ ^ hh with hS
  set Sp := max CL 0 * Θ ^ hh with hSp
  have hSSp : S ≤ Sp := by
    rw [hS, hSp]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hΘ _)
  have hSp0 : 0 ≤ Sp := mul_nonneg (le_max_right _ _) (pow_nonneg hΘ _)
  have hSsq : ENNReal.ofReal S ^ 2 ≤ ENNReal.ofReal (Sp ^ 2) := by
    rw [ENNReal.ofReal_pow hSp0]; gcongr
  -- per-time data
  have hdata : ∀ t ∈ Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      ResidualTimeData π (Set.Icc t₀ t₁) N D Acl (max (kl + 1) (Ll + 2)) f F εc a ℓ ρ t
        ((ℓ ^ 2)⁻¹ * t) S kres Vc := by
    intro t ht
    have hτ : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc t₀ t₁ := by
      constructor
      · rw [le_inv_mul_iff₀ hℓ2]; linarith [ht.1]
      · rw [inv_mul_le_iff₀ hℓ2]; linarith [ht.2]
    exact {
      mass_pos := hset.mass_pos
      ε_nonneg := hεc0
      ε_le := hset.εc_le
      ρ_pos := hρ
      τ_mem := hτ
      τ_eq := by field_simp
      hZ := by omega
      hA := hA
      box := fun n hn => by
        obtain ⟨-, -, -, -, -, c6, c7, -, -, -⟩ :=
          htail n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
        exact ⟨fun m α v u => BoundTail.isBoxSmooth_slow_zero (c6 m α v u _ hτ).1 (by omega),
          fun k m α v u => BoundTail.isBoxSmooth_slow_zero (c7 k m α v u _ hτ).1 (by omega)⟩
      per := fun n hn k m α v u X => by
        obtain ⟨-, -, -, -, -, -, c7, -, -, -⟩ :=
          htail n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
        exact (c7 k m α v u _ hτ).2 X
      zero := fun n hn => by
        obtain ⟨c1, c2, -, -, -, -, -, -, -, -⟩ :=
          htail n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
        exact ⟨fun α t X z v u => c1 0 α t X z v u (Or.inl rfl),
          fun k α t X z v u => c2 k 0 α t X z v u (Or.inl rfl)⟩
      jet := fun n hn i hi m => by
        obtain ⟨-, -, -, -, -, -, -, -, -, c10⟩ :=
          htail n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
        exact c10 i hi m
      order := by omega
      smooth := ha t
      chain := hVc _ hτ }
  -- time integration
  have hpR0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e := by positivity
  have hpq0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl := by positivity
  have hres := residualNorm_le_of_pointwise ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
    (fun t x k => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x k)
    (fun t x => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x)
    (ResidualTimeData.gradDensity π ρ kres a) (by positivity) (by positivity) measurableSet_Icc
    (fun t ht => (hdata t ht).flux_pointwise he heρ Mn hMn hSSp hSp0 hpR0)
    (fun t ht => (hdata t ht).remainder_pointwise he heρ Mn hMn hSSp hSp0 hpq0)
  have hG : ∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁), ResidualTimeData.gradDensity π ρ kres a t
      ≤ ENNReal.ofReal B⁻¹ *
        classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres a ^ 2 :=
    lintegral_gradDensity_le ρ B hB π _ kres a fun v =>
      measurable_classicalGradFactorialSq ρ kres a v fun j hj w => hmeas j hj w v
  have hGs : (∫⁻ t in Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁),
      ResidualTimeData.gradDensity π ρ kres a t) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt B)⁻¹ *
        classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) kres a := by
    refine (ENNReal.rpow_le_rpow hG (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.2 hB.le) (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv]
    norm_num
  have hvol : volume (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (ℓ ^ 2 * (t₁ - t₀))) := by
    have hw := hset.window
    rw [Real.volume_Icc, ENNReal.ofReal_rpow_of_nonneg (by nlinarith) (by norm_num),
      ← Real.sqrt_eq_rpow]
    congr 2; ring
  rw [hvol] at hres
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have h1 : εc * ρ = ℓ * Real.sqrt B := by rw [hεc_eq]; field_simp
  refine residual_bound_combine (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) hres hGs ?_
  rw [residual_scale_flux hν hB hℓ he_eq h1 N, residual_scale_scalar hB hℓ h1 N, ← hZ]
  exact residual_bound_real (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hSp hSp0
    (pow_nonneg hεc0 N) hZ0

end AVRegularity
end
end

section
/-! Facade: `cycle_residual_coarse_flux_of_lift`, the coarse flux residual bound conditional on the
lift grading and structure statements. -/
end
