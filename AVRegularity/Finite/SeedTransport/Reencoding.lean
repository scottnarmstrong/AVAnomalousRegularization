-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.TerminalSeedTransportOfIngredients
import AVRegularity.Finite.SeedTransport.Unique
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget

/-! Seed transport: truncate and restart the terminal field, then use the seed's own lift. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.SeedTransport

theorem terminal_seed_reencoding : TerminalSeedReencodingStatement := by
  intro D Dt Ds bw j₀ Pt lawT rootM rootR seedKt freshKt seedKc φ₀ hφ₀ Gt seed ι henc
    M Kout tp sn tf htp hsn Z₀ Z Zw Zk hZ P freshK ρ θ π cker hρ hν hDs hπ hθ hcoeff hkernel hschur
  classical
  let Ut : CompIn Gt.comps → ℝ → TorusHk 0 ℝ := fun v t => truncateTorusHk (Nat.zero_le Kout) (Z v t)
  let Wt : CompIn Gt.comps → ℝ → TorusHk 1 ℝ := fun v t =>
    truncateTorusHk (Nat.succ_le_succ (Nat.zero_le Kout)) (Zw v t)
  let Yt : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (0 + Dt - 1) ℝ :=
    fun v u γ t => truncateTorusHk (by omega : 0 + Dt - 1 ≤ Kout + Dt - 1) (Zk v u γ t)
  have hcut : Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ (D.κ (M - 1))
      (streamVel (D.Φ (M - 1))) 0 tp tf
      (fun v => truncateTorusHk (Nat.zero_le Kout) (Z₀ v)) (fun _ _ => 0) (fun _ _ => 0) Ut Wt Yt :=
    Construction.Preservation.FullLift.native_reg_solution_truncate Pt seedKt freshKt φ₀ hφ₀ Gt
      (D.κ (M - 1)) tp tf (streamVel (D.Φ (M - 1))) 0 Kout (Nat.zero_le Kout) Z₀ Z Zw Zk hZ
  have hrest := native_reg_solution_restart Pt seedKt freshKt φ₀ hφ₀ Gt (D.κ (M - 1)) tp tf
    (streamVel (D.Φ (M - 1))) 0 _ Ut Wt Yt hcut sn ⟨htp, hsn⟩
  let R := seedKernelOperator P seedKc freshK φ₀ hφ₀ seed M sn tf ρ θ π cker
    hsn hρ hν hDs hπ hθ hcoeff hkernel hschur
  refine ⟨(fun v => Wt (ι.symm v)), R.higherInput (fun v => Wt (ι.symm v)), ?_⟩
  exact reencoded_reg_solution Pt P lawT rootM rootR seedKt freshKt seedKc freshK φ₀ hφ₀
    Gt seed ι henc R rfl rfl rfl (D.hΦ (M - 1)) _ Ut Wt Yt hrest

/-- The complete seed-transport adapter, with neither an ambient cap comparison nor extra premises. -/
theorem terminal_seed_transport_proved : Assembly.TerminalSeedTransportStatement :=
  terminal_seed_transport_of_reencoding terminal_seed_reencoding

end AVRegularity.Finite.SeedTransport
