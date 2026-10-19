-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.CycleComparison.Residual.ChartTransport.Part1
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.Proofs.GenSem.ChainMetric
import AVRegularity.Proofs.Torus.FirstSource

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Physical pointwise native lift bounds after transport by the inverse chart. -/

section
open CycleComparison.Lift FastJets
section GeneralPositiveTransport
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Ordinary chart action at arbitrary radii, from the actual coefficient data. -/
theorem chart_transport_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n P₀ Q N : ℕ}
    {cc : LiftCoeff ι hv} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n P₀ Q cc M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C ρ) (β : DerivativeWord2 r)
    (x : Vec 2) (hinv : Φ (Ψ x) = x) (t : ℝ) (ht : t ∈ Set.Icc a b)
 (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y => liftApply n cc (fun _ Y' => f (Φ (ρ • Y')))
      t (ρ⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v) x‖ ≤
      ChartTransport.compConst C r *
      (∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        ∑ a : Fin (splitTerms (List.ofFn w)).length, finiteLiftWordCount n *
          2 ^ (((splitTerms (List.ofFn w)).get a).1.length +
            2 * ((splitTerms (List.ofFn w)).get a).2.length)) *
      ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let g : Vec 2 → ∀ v, hv v := fun Y => f (Φ (ρ • Y))
  have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hrP hn)
  have hmono := data.mono hrP hrQ
  have hbox := liftApply_component_box_reserve n r r cc (fun _ => g) t v hg
    (fun m hm α u => hmono.box m hm α v u t ht)
  have hreg := CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl ρ e
  have hb := ChartTransport.scalar_word_bound le_rfl hΨ hreg hC hrs (hrse.trans heρ) hJΨ β x
  apply hb.trans
  calc
    _ ≤ ChartTransport.compConst C r *
        (∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
          (∑ a : Fin (splitTerms (List.ofFn w)).length, finiteLiftWordCount n *
            2 ^ (((splitTerms (List.ofFn w)).get a).1.length +
              2 * ((splitTerms (List.ofFn w)).get a).2.length)) *
          ChartTransport.compConst C (P₀ + N) *
          (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
            ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (ChartTransport.compConst_nonneg hC r)
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro w _
      have hi' : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hword := chart_diagonal_word_bound_of_data data hlam hlam1 hn r hrP hrQ
        f hf Φ hΦ hC hJ hrs hrse heρ (List.ofFn w)
        (by simpa only [List.length_ofFn] using hi') (Ψ x) x hinv t ht v
      simpa only [orderedDerivative_eq_odL, List.length_ofFn] using hword
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

/-- Positive physical words after inverse-chart transport, for a radius-generic coefficient row. -/
theorem positive_chart_transport_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n P₀ Q N : ℕ}
    {cc : LiftCoeff ι hv} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n P₀ Q cc M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hn : n ≤ N)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C ρ) (β : DerivativeWord2 r)
    (x : Vec 2) (hinv : Φ (Ψ x) = x) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hzero : ∀ α : DerivativeWord2 0, ∀ X z v u, cc 0 α t X z v u = 0) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y => liftApply n cc (fun _ Y' => f (Φ (ρ • Y')))
      t (ρ⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v) x‖ ≤
      ChartTransport.compConst C r *
      (∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        ∑ a : Fin (splitTerms (List.ofFn w)).length, finiteLiftWordCount n *
          2 ^ (((splitTerms (List.ofFn w)).get a).1.length +
            2 * ((splitTerms (List.ofFn w)).get a).2.length)) *
      ChartTransport.compConst C (P₀ + N) *
        (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
          if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let g : Vec 2 → ∀ v, hv v := fun Y => f (Φ (ρ • Y))
  have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) g :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add hrP hn)
  have hmono := data.mono hrP hrQ
  have hbox := liftApply_component_box_reserve n r r cc (fun _ => g) t v hg
    (fun m hm α u => hmono.box m hm α v u t ht)
  have hreg := CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl ρ e
  have hb := ChartTransport.scalar_word_bound le_rfl hΨ hreg hC hrs (hrse.trans heρ) hJΨ β x
  apply hb.trans
  calc
    _ ≤ ChartTransport.compConst C r *
        (∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
          (∑ a : Fin (splitTerms (List.ofFn w)).length, finiteLiftWordCount n *
            2 ^ (((splitTerms (List.ofFn w)).get a).1.length +
              2 * ((splitTerms (List.ofFn w)).get a).2.length)) *
          ChartTransport.compConst C (P₀ + N) *
          (∑ u, M v u * ∑ j ∈ Finset.range (P₀ + N + 1),
            if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (ChartTransport.compConst_nonneg hC r)
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro w _
      have hi' : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hword := positive_chart_diagonal_word_bound_of_data data hlam hlam1 hn r hrP hrQ
        f hf Φ hΦ hC hJ hrs hrse heρ (List.ofFn w)
        (by simpa only [List.length_ofFn] using hi') (Ψ x) x hinv t ht hzero v
      simpa only [orderedDerivative_eq_odL, List.length_ofFn] using hword
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

end GeneralPositiveTransport
end

/-! Physical pointwise native lift bounds after transport by the inverse chart. -/

section
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_positive_chart_transport_dissipation_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ N)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B εc : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hε0 : 0 ≤ εc) (hε1 : εc ≤ 1)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C (liftLength D G.level))
    (β : DerivativeWord2 r) (x : Vec 2) (hinv : Φ (Ψ x) = x) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * εc ^ n * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y => liftApply n (slotLift.coeff hh n)
      (fun _ Y' => f (Φ (liftLength D G.level • Y'))) t
      ((liftLength D G.level)⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v) x‖) ≤
      Real.sqrt B * nativeChartTransportConstant C (P₀ + N) n r *
        (∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let F : Vec 2 → hr v.1.root := fun Y => liftApply n (slotLift.coeff hh n)
    (fun _ Y' => f (Φ (liftLength D G.level • Y'))) t
    ((liftLength D G.level)⁻¹ • Y) (e⁻¹ • Y) v
  have hreg := nativeSlotLift_chart_diagonal_contDiff slotLift P₀ hreserve hh hhh n hn
    r hrP hrQ f hf Φ hΦ e t ht v
  have hb := positive_chart_word_gradient_bound hr0 F hreg Ψ hΨ hC hrs
    (hrse.trans heρ) hJΨ β x
  let q := Real.sqrt ν * εc ^ n
  have hq : 0 ≤ q := mul_nonneg (Real.sqrt_nonneg ν) (pow_nonneg hε0 n)
  have hd := nativeSlotLift_uniform_coefficient_data slotLift P₀ hreserve hh hhh n hn
  let density := ∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
    finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
    ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
      (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖
  have hden : 0 ≤ density := Finset.sum_nonneg fun u _ => mul_nonneg (hd.nonneg v u)
    (Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (pow_nonneg slotLift.setting.ρ_pos.le _) (norm_nonneg _))
  have hsum : q * (∑ i ∈ Finset.range (r + 1), if i = 0 then 0 else
      ∑ w : DerivativeWord2 i, rs ^ (i - 1) * ‖orderedDerivative w F (Ψ x)‖) ≤
      ∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        Real.sqrt B * ((∑ a : Fin (splitTerms (List.ofFn w)).length, finiteLiftWordCount n *
          2 ^ (((splitTerms (List.ofFn w)).get a).1.length +
            2 * ((splitTerms (List.ofFn w)).get a).2.length)) *
          ChartTransport.compConst C (P₀ + N) * density) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases hi0 : i = 0
    · rw [ite_eq_left hi0, mul_zero]
      exact Finset.sum_nonneg fun w _ => mul_nonneg (Real.sqrt_nonneg B)
        (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ =>
          mul_nonneg (finiteLiftWordCount_nonneg n) (pow_nonneg (by norm_num) _))
          (ChartTransport.compConst_nonneg hC _)) hden)
    · rw [ite_eq_right hi0, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      have hw := nativeSlotLift_positive_chart_diagonal_dissipation_bound slotLift P₀ hreserve
        hh hhh n hn0 hn r hrP hrQ f hf Φ hΦ hC hJ hrs hrse heρ hν hB hc hε0 hε1
        (List.ofFn w) (by simpa only [List.length_ofFn] using Nat.one_le_iff_ne_zero.mpr hi0)
        (by simpa only [List.length_ofFn] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Ψ x) x hinv t ht v
      simpa only [orderedDerivative_eq_odL, List.length_ofFn] using hw
  have hb' := mul_le_mul_of_nonneg_left hb hq
  apply hb'.trans
  calc
    _ = ChartTransport.compConst C r * (q * _) := by ring
    _ ≤ ChartTransport.compConst C r * _ :=
      mul_le_mul_of_nonneg_left hsum (ChartTransport.compConst_nonneg hC r)
    _ = _ := by
      change _ = Real.sqrt B * nativeChartTransportConstant C (P₀ + N) n r * density
      rw [nativeChartTransportConstant]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring
end

/-! Finite native pulse sums preserve the physical input jet reserve. -/

section
open CycleComparison.Lift FastJets
section GeneralPositivePulse
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- The positive pulse keeps every positive degree's scale power and excludes the input value. -/
theorem positive_pulse_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {P₀ Q N H : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (data : ∀ hh ≤ H, ∀ n, 1 ≤ n → n ≤ N →
      AmbientLiftCoefficientData par a b hab lam n P₀ Q (Cc hh n) (M hh))
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C ρ) (β : DerivativeWord2 r)
    (x : Vec 2) (hinv : Φ (Ψ x) = x) (c ε τ : ℝ) (hε : 0 ≤ ε)
    (ht : c⁻¹ * τ ∈ Set.Icc a b) (hdegreeZero : ∀ hh ≤ H, Cc hh 0 = 0)
    (hzero : ∀ hh ≤ H, ∀ n, 1 ≤ n → n ≤ N → ∀ α : DerivativeWord2 0,
      ∀ X z v u, Cc hh n 0 α (c⁻¹ * τ) X z v u = 0) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y => pulsePhysicalLift c ρ e ε N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖ ≤
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        ε ^ (n + 1) * (nativeChartTransportConstant C (P₀ + N) (n + 1) r *
          (∑ u, M hh v u * ∑ j ∈ Finset.range (P₀ + N + 1),
            if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
  let A (hh n : ℕ) (Y : Vec 2) : hv v :=
    liftApply (n + 1) (Cc hh (n + 1)) (fun _ Y' => f (Φ (ρ • Y')))
      (c⁻¹ * τ) (ρ⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v
  have hA (hh : ℕ) (hhh : hh ∈ Finset.range (H + 1))
      (n : ℕ) (hn : n ∈ Finset.range N) : ContDiff ℝ (r : ℕ∞) (A hh n) := by
    have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
    have hnN : n + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    have hg : ContDiff ℝ ((r + (n + 1) : ℕ) : ℕ∞) (fun Y => f (Φ (ρ • Y))) :=
      ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
        (by exact_mod_cast Nat.add_le_add hrP hnN)
    have hmono := (data hh hhH (n + 1) (Nat.succ_pos _) hnN).mono hrP hrQ
    have hbox := liftApply_component_box_reserve (n + 1) r r (Cc hh (n + 1))
      (fun _ Y' => f (Φ (ρ • Y'))) (c⁻¹ * τ) v hg
      (fun m hm α u => hmono.box m hm α v u _ ht)
    exact (CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl ρ e).comp hΨ
  have hp : (fun Y => pulsePhysicalLift c ρ e ε N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) =
      fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        ε ^ (n + 1) • A hh n Y := by
    funext Y
    rw [pulsePhysicalLift_static_expansion]
    refine Finset.sum_congr rfl fun hh hhh => ?_
    rw [Finset.sum_range_succ', hdegreeZero hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh))]
    simp only [liftApply, Pi.zero_apply, zero_apply, Finset.sum_const_zero,
      smul_zero, add_zero, A]
  have hd : orderedDerivative β
      (fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N, ε ^ (n + 1) • A hh n Y) =
      fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        ε ^ (n + 1) • orderedDerivative β (A hh n) Y := by
    rw [MixedTail.orderedDerivative_sum (Finset.range (H + 1)) β
      (fun hh hhh => ContDiff.sum (fun n hn => (hA hh hhh n hn).const_smul (ε ^ (n + 1))))]
    funext Y
    apply Finset.sum_congr rfl
    intro hh hhh
    rw [MixedTail.orderedDerivative_sum (Finset.range N) β
      (fun n hn => (hA hh hhh n hn).const_smul (ε ^ (n + 1)))]
    apply Finset.sum_congr rfl
    intro n hn
    exact congrFun (CoarseFluxDiff.orderedDerivative_const_smul β (ε ^ (n + 1)) (hA hh hhh n hn)) Y
  rw [hp, hd]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hrs.le r)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro hh hhh
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hrs.le r)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε _)]
  rw [mul_left_comm (rs ^ r) (ε ^ (n + 1))]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε _)
  have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
  have hnN : n + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hn)
  have hb := positive_chart_transport_word_bound_of_data (data hh hhH _ (Nat.succ_pos _) hnN)
    hlam hlam1 hnN r hrP hrQ f hf Φ hΦ hC hJ hrs hrse heρ Ψ hΨ hJΨ β x hinv
    (c⁻¹ * τ) ht (hzero hh hhH _ (Nat.succ_pos _) hnN) v
  simpa only [A, nativeChartTransportConstant, mul_assoc] using hb

/-- Ordinary static pulse words at arbitrary slow and fast radii. -/
theorem pulse_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {P₀ Q N H : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (data : ∀ hh ≤ H, ∀ n ≤ N,
      AmbientLiftCoefficientData par a b hab lam n P₀ Q (Cc hh n) (M hh))
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C ρ) (β : DerivativeWord2 r)
    (x : Vec 2) (hinv : Φ (Ψ x) = x) (c ε τ : ℝ) (hε : 0 ≤ ε)
    (ht : c⁻¹ * τ ∈ Set.Icc a b) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y => pulsePhysicalLift c ρ e ε N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖ ≤
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        ε ^ n * (nativeChartTransportConstant C (P₀ + N) n r *
          (∑ u, M hh v u * ∑ j ∈ Finset.range (P₀ + N + 1),
            ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
  let A (hh n : ℕ) (Y : Vec 2) : hv v :=
    liftApply n (Cc hh n) (fun _ Y' => f (Φ (ρ • Y')))
      (c⁻¹ * τ) (ρ⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v
  have hA (hh : ℕ) (hhh : hh ∈ Finset.range (H + 1))
      (n : ℕ) (hn : n ∈ Finset.range (N + 1)) : ContDiff ℝ (r : ℕ∞) (A hh n) := by
    have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) (fun Y => f (Φ (ρ • Y))) :=
      ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
        (by exact_mod_cast Nat.add_le_add hrP hnN)
    have hmono := (data hh hhH n hnN).mono hrP hrQ
    have hbox := liftApply_component_box_reserve n r r (Cc hh n)
      (fun _ Y' => f (Φ (ρ • Y'))) (c⁻¹ * τ) v hg
      (fun m hm α u => hmono.box m hm α v u _ ht)
    exact (CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl ρ e).comp hΨ
  have hp : (fun Y => pulsePhysicalLift c ρ e ε N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) =
      fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        ε ^ n • A hh n Y := by
    funext Y
    exact pulsePhysicalLift_static_expansion c ρ e ε N H Cc Φ Ψ f τ Y v
  have hd : orderedDerivative β
      (fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), ε ^ n • A hh n Y) =
      fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        ε ^ n • orderedDerivative β (A hh n) Y := by
    rw [MixedTail.orderedDerivative_sum (Finset.range (H + 1)) β
      (fun hh hhh => ContDiff.sum (fun n hn => (hA hh hhh n hn).const_smul (ε ^ n)))]
    funext Y
    apply Finset.sum_congr rfl
    intro hh hhh
    rw [MixedTail.orderedDerivative_sum (Finset.range (N + 1)) β
      (fun n hn => (hA hh hhh n hn).const_smul (ε ^ n))]
    apply Finset.sum_congr rfl
    intro n hn
    exact congrFun (CoarseFluxDiff.orderedDerivative_const_smul β (ε ^ n) (hA hh hhh n hn)) Y
  rw [hp, hd]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hrs.le r)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro hh hhh
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hrs.le r)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε _)]
  rw [mul_left_comm (rs ^ r) (ε ^ n)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε _)
  have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hb := chart_transport_word_bound_of_data (data hh hhH _ hnN)
    hlam hlam1 hnN r hrP hrQ f hf Φ hΦ hC hJ hrs hrse heρ Ψ hΨ hJΨ β x hinv
    (c⁻¹ * τ) ht v
  simpa only [A, nativeChartTransportConstant, mul_assoc] using hb

end GeneralPositivePulse
end

/-! Active native pulse fields have the spatial regularity needed for cutoff gluing. -/

section
open CycleComparison.Lift FastJets
section GeneralPulse
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Rectangular coefficient reserves suffice for physical pulse regularity at any radius. -/
theorem pulsePhysicalLift_static_contDiff_of_boxes (c ρ e εc : ℝ) (N H r : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι hv) (Φ Ψ : Vec 2 → Vec 2) (f : Vec 2 → ∀ v, hv v) (τ : ℝ)
    (hf : ContDiff ℝ ((r + N : ℕ) : ℕ∞) f)
    (hΦ : ContDiff ℝ ((r + N : ℕ) : ℕ∞) Φ) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hcoeff : ∀ hh ≤ H, ∀ n ≤ N, ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth r r (fun X z => Cc hh n m α (c⁻¹ * τ) X z v u)) (v : ι) :
    ContDiff ℝ (r : ℕ∞) (fun Y => pulsePhysicalLift c ρ e εc N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) := by
  have he : (fun Y => pulsePhysicalLift c ρ e εc N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) =
      fun Y => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        εc ^ n • liftApply n (Cc hh n) (fun _ Y' => f (Φ (ρ • Y')))
          (c⁻¹ * τ) (ρ⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v := by
    funext Y
    exact pulsePhysicalLift_static_expansion c ρ e εc N H Cc Φ Ψ f τ Y v
  rw [he]
  apply ContDiff.sum
  intro hh hhh
  apply ContDiff.sum
  intro n hn
  have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hg : ContDiff ℝ ((r + n : ℕ) : ℕ∞) (fun Y => f (Φ (ρ • Y))) :=
    ((hf.comp hΦ).comp (contDiff_const_smul _)).of_le
      (by exact_mod_cast Nat.add_le_add_left hnN r)
  have hbox := liftApply_component_box_reserve n r r (Cc hh n) (fun _ Y => f (Φ (ρ • Y)))
    (c⁻¹ * τ) v hg (fun m hm α u => hcoeff hh hhH n hnN m hm α v u)
  exact ((CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl ρ e).comp hΨ).const_smul _

end GeneralPulse

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_pulse_contDiff
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (c e εc τ : ℝ)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    ContDiff ℝ (r : ℕ∞) (fun Y => pulsePhysicalLift c (liftLength D G.level) e εc N H
      slotLift.coeff (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) := by
  apply pulsePhysicalLift_static_contDiff_of_boxes c (liftLength D G.level) e εc N H r
    slotLift.coeff Φ Ψ f τ
    (hf.of_le (by exact_mod_cast Nat.add_le_add_right hrP N))
    (hΦ.of_le (by exact_mod_cast Nat.add_le_add_right hrP N)) hΨ
  intro hh hhh n hn m hm α v u
  have hd := nativeSlotLift_uniform_coefficient_data slotLift P₀ hreserve hh hhh n hn
  have hmono := hd.mono
    (show r ≤ ambientDegreeSlowReserve P₀ (N + slotLift.cap) n by
      unfold ambientDegreeSlowReserve; omega)
    (show r ≤ ambientDegreeFastReserve (max k (L + 2)) slotLift.cap H
        (N + slotLift.cap) hh n by unfold ambientDegreeFastReserve; omega)
  exact hmono.box m hm α v u (c⁻¹ * τ) ht

theorem nativeSlotLift_time_pulse_contDiff
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (chart label : ℝ → Vec 2 → Vec 2) (c e εc τ : ℝ)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a (c * (c⁻¹ * τ))))
    (hchart : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart (c * (c⁻¹ * τ))))
    (hlabel : ContDiff ℝ (r : ℕ∞) (label τ))
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    ContDiff ℝ (r : ℕ∞) (fun Y => pulsePhysicalLift c (liftLength D G.level) e εc N H
      slotLift.coeff chart label a τ Y v) := by
  rw [pulsePhysicalLift_freeze_time]
  exact nativeSlotLift_pulse_contDiff slotLift P₀ hreserve r hrP hrQ _ ha _ hchart _ hlabel c e εc τ ht v
end

/-! The actual native pulse uses one fixed height matrix independent of time and slot. -/

section
open CycleComparison.Lift FastJets
section GeneralPositiveMatrixPulse
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- A radius-generic positive pulse loses only one scale factor and one fixed height matrix. -/
theorem positive_pulse_fixed_matrix_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {P₀ Q N H : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u)
    (data : ∀ hh ≤ H, ∀ n, 1 ≤ n → n ≤ N →
      AmbientLiftCoefficientData par a b hab lam n P₀ Q (Cc hh n) (M hh))
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C ρ) (β : DerivativeWord2 r)
    (x : Vec 2) (hinv : Φ (Ψ x) = x) (c ε τ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht : c⁻¹ * τ ∈ Set.Icc a b) (hdegreeZero : ∀ hh ≤ H, Cc hh 0 = 0)
    (hzero : ∀ hh ≤ H, ∀ n, 1 ≤ n → n ≤ N → ∀ α : DerivativeWord2 0,
      ∀ X z v u, Cc hh n 0 α (c⁻¹ * τ) X z v u = 0) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y => pulsePhysicalLift c ρ e ε N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖ ≤
      ε * (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
        (∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  have hb := positive_pulse_word_bound_of_data Cc M data hlam hlam1 r hrP hrQ f hf
    Φ hΦ hC hJ hrs hrse heρ Ψ hΨ hJΨ β x hinv c ε τ hε ht hdegreeZero hzero v
  apply hb.trans
  exact finite_positive_pulse_degree_height_sum_le H N M hM
    (fun n => nativeChartTransportConstant C (P₀ + N) n r)
    (fun n _ => nativeChartTransportConstant_nonneg hC _ _ _)
    (fun u => ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)
    (fun u => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (pow_nonneg (hrs.trans_le (hrse.trans heρ)).le _) (norm_nonneg _)) v hε hε1

/-- Ordinary pulse words use one fixed height matrix at arbitrary radii. -/
theorem pulse_fixed_matrix_word_bound_of_data
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {P₀ Q N H : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u)
    (data : ∀ hh ≤ H, ∀ n ≤ N,
      AmbientLiftCoefficientData par a b hab lam n P₀ Q (Cc hh n) (M hh))
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (f : Vec 2 → ∀ v, hv v) (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C ρ rs e : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C ρ)
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C ρ) (β : DerivativeWord2 r)
    (x : Vec 2) (hinv : Φ (Ψ x) = x) (c ε τ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht : c⁻¹ * τ ∈ Set.Icc a b) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y => pulsePhysicalLift c ρ e ε N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖ ≤
      (∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (P₀ + N) n r) *
        (∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  have hb := pulse_word_bound_of_data Cc M data hlam hlam1 r hrP hrQ f hf
    Φ hΦ hC hJ hrs hrse heρ Ψ hΨ hJΨ β x hinv c ε τ hε ht v
  apply hb.trans
  exact finite_pulse_degree_height_sum_le H N M hM
    (fun n => nativeChartTransportConstant C (P₀ + N) n r)
    (fun n _ => nativeChartTransportConstant_nonneg hC _ _ _)
    (fun u => ∑ j ∈ Finset.range (P₀ + N + 1),
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)
    (fun u => Finset.sum_nonneg fun j _ =>
      mul_nonneg (pow_nonneg (hrs.trans_le (hrse.trans heρ)).le _) (norm_nonneg _)) v hε hε1

end GeneralPositiveMatrixPulse

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}
end

/-! The native pulse bound at its literal physical time uses the same fixed matrix. -/

section
open CycleComparison.Lift FastJets
section GeneralRadiusAction
variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Physical-time pulse words at arbitrary radii, with a fixed height matrix. -/
theorem time_pulse_fixed_matrix_word_bound_of_data
    {par : Fin 2} {tlo thi lam : ℝ} {hab : tlo ≤ thi} {P₀ Q N H : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u)
    (data : ∀ hh ≤ H, ∀ n ≤ N,
      AmbientLiftCoefficientData par tlo thi hab lam n P₀ Q (Cc hh n) (M hh))
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q)
    (c εc τ : ℝ) (hc : c ≠ 0)
    (a : ℝ → Vec 2 → ∀ v : ι, hv v)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart τ))
    {C ρ : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound (chart τ) (P₀ + N) C ρ)
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (label : ℝ → Vec 2 → Vec 2) (hlabel : ContDiff ℝ (r : ℕ∞) (label τ))
    (hJΨ : ChartTransport.JetBound (label τ) r C ρ)
    (β : DerivativeWord2 r) (x : Vec 2) (hinv : chart τ (label τ x) = x) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (ht : c⁻¹ * τ ∈ Set.Icc tlo thi)
    (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y =>
      pulsePhysicalLift c ρ e εc N H Cc
        chart label a τ Y v) x‖ ≤
      (∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (P₀ + N) n r) *
        ∑ u, (∑ hh ∈ Finset.range (H + 1),
          M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), ρ ^ j *
            ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖ := by
  have hclock : c * (c⁻¹ * τ) = τ := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [pulsePhysicalLift_freeze_time, hclock]
  exact pulse_fixed_matrix_word_bound_of_data Cc M hM data hlam hlam1 r hrP hrQ
    (a τ) ha (chart τ) hchart hC hJ hrs hrse heρ (label τ) hlabel hJΨ β x hinv c εc τ hεc hεc1 ht v

end GeneralRadiusAction
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
section
/-! Finite native pulse sums preserve the physical input jet reserve. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_pulse_dissipation_word_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C (liftLength D G.level))
    (β : DerivativeWord2 r) (x : Vec 2) (hinv : ∀ Y, Φ (Ψ Y) = Y) (c εc τ : ℝ) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
      pulsePhysicalLift c (liftLength D G.level) e εc N H slotLift.coeff
        (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖) ≤
      Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y => f Y v) x‖) +
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        Real.sqrt B * nativeChartTransportConstant C (P₀ + N) (n + 1) r *
          (∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
            ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
              (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  let A (hh n : ℕ) (Y : Vec 2) : hr v.1.root :=
    liftApply (n + 1) (slotLift.coeff hh (n + 1))
      (fun _ Y' => f (Φ (liftLength D G.level • Y'))) (c⁻¹ * τ)
      ((liftLength D G.level)⁻¹ • Ψ Y) (e⁻¹ • Ψ Y) v
  have hA (hh : ℕ) (hhh : hh ∈ Finset.range (H + 1))
      (n : ℕ) (hn : n ∈ Finset.range N) : ContDiff ℝ (r : ℕ∞) (A hh n) :=
    (nativeSlotLift_chart_diagonal_contDiff slotLift P₀ hreserve hh
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) (n + 1)
      (Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)) r hrP hrQ f hf Φ hΦ e (c⁻¹ * τ) ht v).comp hΨ
  have hfcomp : ContDiff ℝ (r : ℕ∞) (fun Y => f Y v) :=
    ((ContinuousLinearMap.proj v).contDiff.comp hf).of_le
      (by exact_mod_cast hrP.trans (Nat.le_add_right P₀ N))
  have hp : (fun Y => pulsePhysicalLift c (liftLength D G.level) e εc N H slotLift.coeff
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) =
      fun Y => f Y v + ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        εc ^ (n + 1) • A hh n Y := by
    funext Y
    exact nativeSlotLift_pulse_positive_degree_expansion slotLift f Φ Ψ Y (hinv Y) c e εc τ ht v
  have hd : orderedDerivative β
      (fun Y => f Y v + ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
        εc ^ (n + 1) • A hh n Y) =
      fun Y => orderedDerivative β (fun Y => f Y v) Y +
        ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
          εc ^ (n + 1) • orderedDerivative β (A hh n) Y := by
    rw [AVRegularity.orderedDerivative_add β hfcomp
      (ContDiff.sum fun hh hhh => ContDiff.sum fun n hn => (hA hh hhh n hn).const_smul _)]
    rw [MixedTail.orderedDerivative_sum (Finset.range (H + 1)) β
      (fun hh hhh => ContDiff.sum fun n hn => (hA hh hhh n hn).const_smul _)]
    funext Y
    congr 1
    refine Finset.sum_congr rfl fun hh hhh => ?_
    rw [MixedTail.orderedDerivative_sum (Finset.range N) β
      (fun n hn => (hA hh hhh n hn).const_smul _)]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact congrFun (CoarseFluxDiff.orderedDerivative_const_smul β (εc ^ (n + 1)) (hA hh hhh n hn)) Y
  rw [hp, hd]
  have hweight : 0 ≤ Real.sqrt ν * rs ^ (r - 1) :=
    mul_nonneg (Real.sqrt_nonneg ν) (pow_nonneg hrs.le _)
  simp only [← mul_assoc]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) hweight).trans
  rw [mul_add]
  apply add_le_add_right
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hweight).trans
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun hh hhh => ?_
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hweight).trans
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hεc _)]
  have hb := nativeSlotLift_positive_chart_transport_dissipation_bound slotLift P₀ hreserve hh
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) (n + 1) (by omega)
    (Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)) r hr0 hrP hrQ f hf Φ hΦ hC hJ
    hrs hrse heρ hν hB hc hεc hεc1 Ψ hΨ hJΨ β x (hinv x) (c⁻¹ * τ) ht v
  simpa only [A, mul_assoc, mul_left_comm (rs ^ (r - 1)) (εc ^ (n + 1))] using hb

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Native pulse dissipation with one matrix independent of space and time. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_pulse_fixed_matrix_dissipation_word_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C (liftLength D G.level))
    (β : DerivativeWord2 r) (x : Vec 2) (hinv : ∀ Y, Φ (Ψ Y) = Y) (c εc τ : ℝ) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
      pulsePhysicalLift c (liftLength D G.level) e εc N H slotLift.coeff
        (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖) ≤
      Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y => f Y v) x‖) +
      Real.sqrt B * (∑ n ∈ Finset.range N,
        nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
          (∑ u, (∑ hh ∈ Finset.range (H + 1),
            nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
            ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
              (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
  have hb := nativeSlotLift_pulse_dissipation_word_bound slotLift P₀ hreserve r hr0 hrP hrQ
    f hf Φ hΦ hC hJ hrs hrse heρ Ψ hΨ hJΨ β x hinv c εc τ hεc hεc1 hν hB hc ht v
  apply hb.trans_eq
  congr 1
  calc
    _ = Real.sqrt B * (∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
      nativeChartTransportConstant C (P₀ + N) (n + 1) r *
        ∑ u, (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [finite_pulse_degree_height_sum_eq (Finset.range (H + 1)) (Finset.range N)
        (fun hh v u => nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u)
        (fun n => nativeChartTransportConstant C (P₀ + N) (n + 1) r)
        (fun u => ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
          (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖) v]
      rw [mul_assoc]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The torus proof uses diffusivity positivity only to make the current cell time
scale nonnegative. This local form applies to a finite band chain without imposing values
on its unconstrained tail. The two flux arguments are those of the torus case. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Providers.Torus AVRegularity.Providers.GenSem

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]

/-- An actual step preserves the base and slow-offset torus laws using only its cell time scale. -/
theorem successor_shift_invariant_of_cellScaleSq_nonneg
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
    {M : ℕ} {G G' : GenStage D hr Dm b j₀}
    (hζ : IsFastProfile D.ζ) (hcs : 0 ≤ D.cellScaleSq G.level)
    (hnat : G.IsNatural M) (hsh : G.IsShiftInvariant)
    (hsucc : IsActualSuccessor D P Mn G G') : G'.IsShiftInvariant := by
  classical
  have hτ := Uniqueness.ocTau_pos_of_natural hnat
  have hbase : ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ),
      c'.1 = c.1.shiftBase n → ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d-1)),
        G'.fam.flux p c' v u γ d I = G'.fam.flux p c v u γ d I := by
    intro p c c' n hc v u γ d I
    funext t X z
    by_cases hd : 2 ≤ d
    · by_cases hdg : ∃ m, G'.prov v u γ = Prov.letter m .diag []
      ·
        obtain ⟨-, -, -, -, -, -, e, _, Cc0, -, hDL, hmain⟩ := hsucc
        obtain ⟨hp, -, -, hfl⟩ := hmain v u γ
        have hdg' : (e v u γ).1.IsDiag := by
          obtain ⟨m, hm⟩ := hdg
          have hps : (e v u γ).1.prov G.level = Prov.letter m .diag [] := hp ▸ hm
          generalize (e v u γ).1 = s at hps ⊢
          cases s with
          | letterDiag => trivial
          | _ => simp [SuccSource.prov] at hps
        rw [hfl hdg' p c' d I t X z hd, hfl hdg' p c d I t X z hd, hc, recenter_shiftBase]
        by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        · have hadm' : IsAdmissibleChain D b j₀ G'.level p.1
              ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
          rw [ite_eq_left hadm', ite_eq_left hadm, firstSourceFlux_shiftBase hζ hτ hcs hDL]
        · have hadm' : ¬ IsAdmissibleChain D b j₀ G'.level p.1
              ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
          rw [ite_eq_right hadm', ite_eq_right hadm]
      · have hnd : ∀ m, G'.prov v u γ ≠ Prov.letter m .diag [] :=
          fun m hm => hdg ⟨m, hm⟩
        obtain ⟨-, -, -, -, -, -, e, Cc, _, hLF, -, hmain⟩ := hsucc
        obtain ⟨hp, -, hfl, -⟩ := hmain v u γ
        have hnd' : ¬ (e v u γ).1.IsDiag := by
          have hdiag : ∀ s : SuccSource G, s.prov G.level = G'.prov v u γ → ¬ s.IsDiag := by
            intro s hps hdg
            cases s <;> simp only [SuccSource.IsDiag] at hdg
            exact hnd G.level (by rw [← hps]; rfl)
          exact hdiag _ hp.symm
        rw [hfl hnd' p c' d I t X z hd, hfl hnd' p c d I t X z hd, hc, recenter_shiftBase]
        by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        · have hadm' : IsAdmissibleChain D b j₀ G'.level p.1
              ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
          rw [ite_eq_left hadm', ite_eq_left hadm]
          exact transferAt_shiftBase D _ _ _ _ _ t _ z n d I fun k hk d' I' =>
            fluxCoeff_fluxOp_shiftBase hζ hsh hτ hcs _ _ (hLF _) n hk _ d' I'
        · have hadm' : ¬ IsAdmissibleChain D b j₀ G'.level p.1
              ((c.1.recenter D (D.eps (G'.level - 1) • X)).shiftBase n) := hadm
          rw [ite_eq_right hadm', ite_eq_right hadm]
    · rw [G'.fam.flux_zero p c' v u γ d I (fun h => hd h.1),
        G'.fam.flux_zero p c v u γ d I (fun h => hd h.1)]
  exact ⟨hbase, hsucc.slowOffset' hbase⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Native pulse dissipation with one matrix independent of space and time. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_pulse_physical_dissipation_word_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (f : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hf : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) Φ)
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound Φ (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (Ψ : Vec 2 → Vec 2) (hΨ : ContDiff ℝ (r : ℕ∞) Ψ)
    (hJΨ : ChartTransport.JetBound Ψ r C (liftLength D G.level))
    (β : DerivativeWord2 r) (x : Vec 2) (hinv : ∀ Y, Φ (Ψ Y) = Y) (c εc τ : ℝ) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hc : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
      pulsePhysicalLift c (liftLength D G.level) e εc N H slotLift.coeff
        (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ Y v) x‖) ≤
      Real.sqrt B * ((∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
        (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X v) x‖) + (∑ n ∈ Finset.range N,
        nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
          (∑ u, (∑ hh ∈ Finset.range (H + 1),
            nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
            ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
              (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => f X u) x‖)) := by
  have hb := nativeSlotLift_pulse_fixed_matrix_dissipation_word_bound slotLift P₀ hreserve r hr0 hrP hrQ
    f hf Φ hΦ hC hJ hrs hrse heρ Ψ hΨ hJΨ β x hinv c εc τ hεc hεc1 hν hB hc ht v
  have hfv : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (fun X => f X v) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun v : CompIn G.comps => hr v.1.root) v).contDiff.comp hf
  have hcoarse := physical_positive_jet_density_dissipation_le hr0
    (hrP.trans (Nat.le_add_right P₀ N)) (fun X => f X v) hfv hrs (hrse.trans heρ) hνB β x
  apply hb.trans
  apply (add_le_add_left hcoarse _).trans_eq
  ring

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Only active pulse regularity is needed for the literal finite glued field. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_contDiff
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c e εc τ : ℝ) (hc : c ≠ 0)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    ContDiff ℝ (r : ℕ∞) (fun Y => gluedLift kset ϖ c (liftLength D G.level) e εc N H
      (nativeStageLiftFamily slotLifts) chart label a τ Y v) := by
  classical
  have hclock : c * (c⁻¹ * τ) = τ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  simp only [gluedLift, Finset.sum_apply, Pi.smul_apply]
  apply ContDiff.sum
  intro j hj
  by_cases hw : ϖ j τ = 0
  · simpa only [hw, zero_smul] using (contDiff_const : ContDiff ℝ (r : ℕ∞) (fun _ : Vec 2 => (0 : hr v.1.root)))
  · apply ContDiff.const_smul
    simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
    apply nativeSlotLift_time_pulse_contDiff (slotLifts ⟨j, hodd j hj⟩) P₀
      (hreserve _) r hrP hrQ a (chart j) (label j) c e εc τ
    · simpa only [hclock] using ha
    · simpa only [hclock] using hchart j hj hw
    · exact hlabel j hj hw
    · exact ht j hj hw

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The native pulse bound at its literal physical time uses the same fixed matrix. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeSlotLift_time_pulse_dissipation_word_bound
    (slotLift : NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ) (hreserve : P₀ + (N + slotLift.cap) ≤ K + 4 * (H + 1) * (N + slotLift.cap) ^ 2)
    (r : ℕ) (hr0 : 1 ≤ r) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (c εc τ : ℝ) (hc : c ≠ 0)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart τ))
    {C : ℝ} (hC : 1 ≤ C)
    (hJ : ChartTransport.JetBound (chart τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (label : ℝ → Vec 2 → Vec 2) (hlabel : ContDiff ℝ (r : ℕ∞) (label τ))
    (hJΨ : ChartTransport.JetBound (label τ) r C (liftLength D G.level))
    (β : DerivativeWord2 r) (x : Vec 2) (hinv : ∀ Y, chart τ (label τ Y) = Y) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (ht : c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level slot.1 / D.cellScaleSq G.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    Real.sqrt ν * (rs ^ (r - 1) * ‖orderedDerivative β (fun Y =>
      pulsePhysicalLift c (liftLength D G.level) e εc N H slotLift.coeff
        chart label a τ Y v) x‖) ≤
      Real.sqrt B * ((∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
        (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X v) x‖) + (∑ n ∈ Finset.range N,
        nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
          (∑ u, (∑ hh ∈ Finset.range (H + 1),
            nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
              finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
            ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
              (liftLength D G.level) ^ (j - 1) * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖)) := by
  have hclock : c * (c⁻¹ * τ) = τ := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [pulsePhysicalLift_freeze_time, hclock]
  exact nativeSlotLift_pulse_physical_dissipation_word_bound slotLift P₀ hreserve r hr0 hrP hrQ
    (a τ) ha (chart τ) hchart hC hJ hrs hrse heρ (label τ) hlabel hJΨ β x hinv c εc τ
    hεc hεc1 hν hB hνB hprice ht v

end AVRegularity.Construction.Preservation.FullLift
end
end
end
