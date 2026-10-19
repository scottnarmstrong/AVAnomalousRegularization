-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.EntryWeak.WeakReduction
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Finite.SeedTransport.Reencoding
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Construction.Scales.Times

@[expose] public section

section
namespace AVRegularity.Providers

/-! Proof of `finite_order_choice`.

The choices are made in the order of the statement's docstring: `Q_T`; then `N_T, p_T, R_T, A_T`; then
`t_T = δ/(16(s_T+1))`, which keeps `b_T ≥ δ(27/32 - 1/16) > 0`; then the moments; then
`τ_entry = min{qχ_w, b_T}/2`, and `λ_entry` the midpoint between `3δ` and the smaller width
exponent (`width_exponent_gaps`). -/

/-- A natural number with `a * n > B` for `a > 0`. -/
theorem exists_nat_mul_gt {a : ℝ} (ha : 0 < a) (B : ℝ) : ∃ n : ℕ, a * n > B := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / a)
  exact ⟨n, by rw [div_lt_iff₀ ha] at hn; linarith⟩

/-- **The order choice of the finite theorem**. -/
theorem finite_order_choice (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) :
    ∀ (Jw Nw Rw Lw : ℕ) (η₀ PT : ℝ), 1 ≤ Jw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 → 0 < PT →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) →
    ∃ (QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT : ℝ),
      IsTerminalSchedule α q s PT QT σw (weakChi α q η₀) η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT
        LpT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) ∧ Jw * Nw + 6 ≤ k₀ ∧
    ∃ τe lamE : ℝ,
      IsEntrySeedExponents α q σw (weakChi α q η₀) η₀ tT τe lamE NT pT (1 + Jw * Nw) (Jw * Rw) := by
  intro Jw Nw Rw Lw η₀ PT _hJw hη₀ hηδ _hPT σw hσw _hσw₁
  obtain ⟨hγ, hδ, -, -, -, -⟩ := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hq0 : 0 < q := by linarith [hq.1]
  set δ := ocDelta α q with hδdef
  set ζ := q * ocGamma α q + 3 * δ with hζdef
  have hζ : 0 < ζ := by positivity
  set χ := weakChi α q η₀ with hχdef
  have hχ : 0 < χ := weakChi_pos hα₀ hq.1 hq.2.1 hηδ
  -- `Q_T`
  set QT : ℝ := 2 * (PT + q ^ (Jw + 1) * (1 + s) + 3) with hQT
  -- physical menus
  obtain ⟨AT, hAT⟩ := exists_nat_mul_gt hζ 3
  obtain ⟨NT, hNT⟩ := exists_nat_mul_gt hζ (QT + 2)
  obtain ⟨RT, hRT⟩ := exists_nat_mul_gt (show 0 < δ / 2 by positivity) (QT + 2)
  obtain ⟨pT, hpT⟩ := exists_nat_mul_gt hδ (QT + 2)
  -- the fresh-letter width
  set A := termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw) with hA
  set sT : ℝ := (termExcess NT pT A : ℝ) with hsT
  have hsT0 : 0 ≤ sT := Nat.cast_nonneg _
  set tT : ℝ := δ / (16 * (sT + 1)) with htT
  have htT0 : 0 < tT := by positivity
  have htT1 : tT < δ / (8 * (sT + 1)) := by
    rw [htT]; apply div_lt_div_of_pos_left hδ (by positivity); linarith
  have htsT : tT * sT ≤ δ / 16 := by
    rw [htT, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set bT : ℝ := δ - η₀ - η₀ / 4 - tT * sT with hbT
  have hbT : 0 < bT := by rw [hbT]; linarith
  -- moments
  obtain ⟨LcT, hLc⟩ := exists_nat_mul_gt htT0 (QT + 2 - bT)
  obtain ⟨LoT, hLo⟩ := exists_nat_mul_gt (show 0 < ζ + q * σw by positivity) (QT + 2 - q * χ)
  obtain ⟨LfT, hLf⟩ := exists_nat_mul_gt (show 0 < q * σw by positivity) (QT + 2 - q * χ)
  obtain ⟨LpT, hLp⟩ := exists_nat_mul_gt (show 0 < q * σw by positivity) (2 * QT + 4 - q * χ)
  -- seed exponents
  obtain ⟨hw1, hw2⟩ := AVRegularity.EntryScales.width_exponent_gaps hα₀ hα₁ hs₀ hs₁ hq hσw htT0
  set W : ℝ := min (q ^ 2 * (1 + σw) - 1 - ocC α q) (q * (1 + ocC α q + tT) - 1 - ocC α q)
  have hW : 3 * δ < W := lt_min hw1 (by linarith)
  refine ⟨QT, NT, pT, RT, AT, Lw + Jw * Nw + 6, LcT, LoT, LfT, LpT, tT, ?_, by omega,
    min (q * χ) bT / 2, (3 * δ + W) / 2, ?_⟩
  · refine ⟨by omega, ?_, by linarith, by linarith, ?_, by linarith, hη₀, hηδ, htT0, htT1, ?_,
      ?_, ?_, ?_⟩
    · rw [hQT]; linarith
    · linarith
    · show bT + tT * LcT > QT + 2; linarith
    · show q * χ + (ζ + q * σw) * LoT > QT + 2; linarith
    · show q * (χ + σw * LfT) > QT + 2; nlinarith
    · show q * (χ + σw * LpT) > 2 * QT + 4; nlinarith
  · have hm : 0 < min (q * χ) bT := lt_min (by positivity) hbT
    refine ⟨by positivity, ?_, ?_, by linarith, ?_, ?_⟩
    · linarith [min_le_left (q * χ) bT]
    · show min (q * χ) bT / 2 < bT; linarith [min_le_right (q * χ) bT]
    · linarith [min_le_left (q ^ 2 * (1 + σw) - 1 - ocC α q)
        (q * (1 + ocC α q + tT) - 1 - ocC α q)]
    · linarith [min_le_right (q ^ 2 * (1 + σw) - 1 - ocC α q)
        (q * (1 + ocC α q + tT) - 1 - ocC α q)]

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! Proof of the terminal-to-seed transport, with the exact premises. -/

/-- **Terminal-to-seed solution transport**. -/
theorem terminal_seed_transport {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}
    (Pt : ProvParams) (lawT : BirthLaw) (rootM rootR : ℕ → ℝ)
    (seedKt freshKt seedKc : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (Gt : GenStage D ScalarH Dt b j₀) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (M Kout : ℕ) (tp sn tf : ℝ) (htp : tp ≤ sn) (hsn : sn ≤ tf)
    (Z₀ : ∀ v : CompIn Gt.comps, TorusHk Kout (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root))
    (Zw : ∀ v : CompIn Gt.comps, ℝ → TorusHk (Kout + 1) (ScalarH v.1.root))
    (Zk : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (Kout + Dt - 1) (ScalarH u.1.root))
    (hZ : Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) Kout tp
      tf Z₀ (fun _ _ => 0) (fun _ _ => 0) Z Zw Zk) :
    ∀ (P : ProvParams) (freshK : ℕ → KernelSpec)
      (ρ θ : ℝ) (π : CompIn seed.comps → ℝ) (cker : ℕ → ℝ),
      0 < ρ → 0 < D.κ (M - 1) → 2 ≤ Ds → (∀ w, 0 < π w) → θ ≤ 1 / 8 →
      (∀ w u (γ : seed.fam.Γ w u) (d : ↥(Finset.Icc 2 Ds)),
        (Measurable fun q : Set.Icc sn tf × Vec 2 => seed.physCoeff w u γ d.1 q.1 q.2) ∧
        (∀ t ∈ Set.Icc sn tf, ContDiff ℝ (0 : ℕ) (seed.physCoeff w u γ d.1 t)) ∧
        (∀ t ∈ Set.Icc sn tf, AVenhance.IsZ2Periodic (seed.physCoeff w u γ d.1 t)) ∧
        coefficientSeminorm ρ 0 sn tf (seed.physCoeff w u γ d.1) ≠ ⊤) →
      (∀ w u (γ : seed.fam.Γ w u),
        0 < (seed.kernelOf P seedKc freshK w u γ).width ∧
        IsSpatialRegularizerTorus ρ 0 Ds sn tf cker (seed.kernelOf P seedKc freshK w u γ).width
          (seed.sysS P seedKc freshK φ₀ hφ₀ w u γ)) →
      SchurBound θ (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun w => ScalarH w.1.root)
        (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.κ (M - 1)) ρ π 0 Ds sn tf cker
        (fun w u γ => (seed.kernelOf P seedKc freshK w u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun w u γ d => seed.physCoeff w u γ d.1)) →
      (∃ (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
          (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root)),
        seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1))) 0 sn tf
          (fun w => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) sn))
          (fun _ _ => 0) (fun _ _ => 0)
          (fun w t => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) t)) Uw Uk) ∧
      ∀ (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
        (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
        (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root)),
        seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1))) 0 sn tf
          (fun w => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) sn))
          (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
        ∀ w, ∀ t ∈ Set.Icc sn tf, U w t = truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) t) := by
  exact Finite.SeedTransport.terminal_seed_transport_proved Pt lawT rootM rootR seedKt freshKt seedKc
    φ₀ hφ₀ Gt seed ι henc M Kout tp sn tf htp hsn Z₀ Z Zw Zk hZ

end AVRegularity.Providers
end
