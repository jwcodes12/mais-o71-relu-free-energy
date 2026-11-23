import TheoremB

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal Topology
namespace O71

theorem prior_sublevel (e : ℝ) :
    prior.real {w | populationLoss w ≤ e} = (volume (physicalSublevel e)).toReal / ballMass := by
  rw [measureReal_def,cond_apply Metric.isClosed_closedBall.measurableSet,ENNReal.toReal_mul,ENNReal.toReal_inv]
  change ballMass⁻¹ * (volume (physicalSublevel e)).toReal = _
  ring

theorem populationLoss_nontrivial : ∃ w ∈ ballW, 0 < populationLoss w := by
  let w : Space := WithLp.toLp 2 ![(1/4:ℝ),1,0,0,1,0,0,1,0,0]
  have hr : radiusSq (physical w) = 1/16 := by norm_num [w,physical,radiusSq,Fin.sum_univ_three]
  rw [physical_radius] at hr
  refine ⟨w,?_,?_⟩
  · change dist w center ≤ 1/3
    nlinarith [dist_nonneg (x := w) (y := center)]
  · norm_num [w,populationLoss,prediction,center,intervalIntegral.integral_const]

/-- Theorem B with the literal free energy and empirical entropy. -/
theorem freeEnergy_upper : boundedAboveInProbability (fun n s =>
    freeEnergy s - n*empiricalEntropy s - (11/6)*log n + (1/3)*log (log n)) := by
  intro η hη
  obtain ⟨M,h⟩ := theorem_B η hη
  refine ⟨M,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℕ)] with n hn hn0
  simpa only [freeEnergy_excess hn0.ne',residual,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero] using hn

/-- At every fixed real threshold, the probability of remaining above it tends to zero. -/
theorem freeEnergy_diverges_to_neg_inf (T : ℝ) :
    Tendsto (fun n => (sampleLaw n).real {s |
      T ≤ freeEnergy s - n*empiricalEntropy s - (11/6)*log n}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => hb.trans_le measureReal_nonneg
  · intro b hb
    filter_upwards [divergence_of_theoremB theorem_B T (b/2) (by positivity),
      eventually_gt_atTop (0:ℕ)] with n hn hn0
    suffices (sampleLaw n).real {s | T ≤ freeEnergy s - n*empiricalEntropy s - (11/6)*log n} ≤ b/2 by linarith
    simpa only [freeEnergy_excess hn0.ne',residual,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero] using hn

/-- Corollary 1. Both displays are written with the same three existential witnesses. -/
theorem mais_o71_refutation : ¬ ∃ (a : ℝ) (m : ℕ) (C : ℝ), 0 < a ∧ 1 ≤ m ∧ 0 < C ∧
    Tendsto (fun e : ℝ => prior.real {w | populationLoss w ≤ e} /
      (e^a * (log (1/e))^(m-1))) (𝓝[>] 0) (𝓝 C) ∧
    boundedInProbability (fun n s => freeEnergy s - n*empiricalEntropy s - a*log n +
      ((m-1 : ℕ) : ℝ)*log (log n)) := by
  rintro ⟨a,m,C,ha,hm,hC,h1,h2⟩
  apply refutation_of_theoremB theorem_B ⟨a,m,C,ha,hm,hC,?_,?_⟩
  · simpa only [prior_sublevel,displayOne,ballMass] using h1
  · intro η hη
    obtain ⟨M,hM⟩ := h2 η hη
    refine ⟨M,?_⟩
    filter_upwards [hM,eventually_gt_atTop (0:ℕ)] with n hn hn0
    simpa only [freeEnergy_excess hn0.ne',residual] using hn

theorem centered_freeEnergy_not_tight : ¬ boundedInProbability (fun n s =>
    freeEnergy s - n*empiricalEntropy s - (11/6)*log n) := by
  intro ht
  obtain ⟨C,hC,hA⟩ := uniform_prior_asymptotic
  apply mais_o71_refutation ⟨11/6,1,C,by norm_num,by norm_num,hC,?_,?_⟩
  · simpa only [prior_sublevel,ballMass,Nat.sub_self,pow_zero,mul_one] using hA
  · simpa only [Nat.sub_self,Nat.cast_zero,zero_mul,add_zero] using ht

/-- The same negation with the multiplicity quantified over the integers as in
the original question. On m ≥ 1 its integer log-power equals the natural power. -/
theorem mais_o71_refutation_integer : ¬ ∃ (a : ℝ) (m : ℤ) (C : ℝ), 0 < a ∧ 1 ≤ m ∧ 0 < C ∧
    Tendsto (fun e : ℝ => prior.real {w | populationLoss w ≤ e} /
      (e^a * (log (1/e))^(m-1))) (𝓝[>] 0) (𝓝 C) ∧
    boundedInProbability (fun n s => freeEnergy s - n*empiricalEntropy s - a*log n +
      ((m-1 : ℤ) : ℝ)*log (log n)) := by
  rintro ⟨a,m,C,ha,hm,hC,h1,h2⟩
  lift m to ℕ using (by omega : 0 ≤ m)
  have hz : ((m-1 : ℕ) : ℤ) = (m:ℤ)-1 := by omega
  apply mais_o71_refutation ⟨a,m,C,ha,by omega,hC,?_,?_⟩
  · simpa only [←hz,zpow_natCast] using h1
  · simpa only [←hz,Int.cast_natCast] using h2

#print axioms mais_o71_refutation_integer
#print axioms centered_freeEnergy_not_tight
#print axioms populationLoss_nontrivial
#print axioms freeEnergy_upper
#print axioms freeEnergy_diverges_to_neg_inf
#print axioms mais_o71_refutation
end O71
