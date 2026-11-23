import Likelihood

noncomputable section
open MeasureTheory Real Filter Set ProbabilityTheory
open scoped ENNReal
namespace O71

theorem input_interval (t d : ℝ) (hd : 0 ≤ d) :
    inputLaw (Icc t (t+d)) ≤ ENNReal.ofReal d := by
  rw [cond_apply measurableSet_Icc]
  have h := measure_mono (inter_subset_right (s := Icc (-1:ℝ) 1) (t := Icc t (t+d))) (μ := volume)
  rw [Real.volume_Icc,add_sub_cancel_left] at h
  rw [Real.volume_Icc]
  norm_num
  exact (mul_le_of_le_one_left' (by norm_num : (2:ℝ≥0∞)⁻¹ ≤ 1)).trans h

/-- The nonexceptional exponent costs a per-point, deterministic amount. A larger
exponent on U costs only its uniform-input probability times its size. -/
theorem kernel_bound {n : ℕ} {f g : ℝ → ℝ} {U : Set ℝ} {a b u : ℝ}
    (hU : MeasurableSet U) (hu : inputLaw U ≤ ENNReal.ofReal u) (hu' : 0 ≤ u)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hf : ∀ x ∈ Icc (-1:ℝ) 1, x ∉ U → f x*g x ≤ a)
    (hg : ∀ x ∈ Icc (-1:ℝ) 1, x ∈ U → f x*g x ≤ b) :
    (∫⁻ x, eexp (f x*g x) ∂inputLaw)^n ≤ eexp (n*(2*a+2*b*u)) := by
  have hlin (v : ℝ) (hv : v ∈ Icc 0 1) : exp v ≤ 1+2*v := by
    have h := abs_exp_sub_one_le (x := v) (by simpa [abs_of_nonneg hv.1] using hv.2)
    rw [abs_of_nonneg hv.1] at h
    linarith [(abs_le.mp h).2]
  let base := ENNReal.ofReal (1+2*a)
  let addend := ENNReal.ofReal (2*b)
  have hmajor : ∀ᵐ x ∂inputLaw, eexp (f x*g x) ≤ base + U.indicator (fun _ => addend) x := by
    apply ae_cond_of_forall_mem measurableSet_Icc
    intro x hx
    by_cases h : x ∈ U
    · rw [indicator_of_mem h]
      unfold base addend eexp
      rw [← ENNReal.ofReal_add (by linarith [ha.1]) (by linarith [hb.1])]
      apply ENNReal.ofReal_le_ofReal
      linarith [(exp_le_exp.mpr (hg x hx h)).trans (hlin b hb),ha.1]
    · rw [indicator_of_notMem h,add_zero]
      exact ENNReal.ofReal_le_ofReal ((exp_le_exp.mpr (hf x hx h)).trans (hlin a ha))
  have h := lintegral_mono_ae hmajor
  rw [lintegral_add_left measurable_const,lintegral_indicator hU,setLIntegral_const] at h
  simp only [lintegral_const,measure_univ,mul_one] at h
  have h' : (∫⁻ x, eexp (f x*g x) ∂inputLaw) ≤ eexp (2*a+2*b*u) := by
    refine h.trans ?_
    calc
      _ ≤ base + addend * ENNReal.ofReal u := by gcongr
      _ = ENNReal.ofReal (1+2*a+2*b*u) := by
        unfold base addend
        rw [← ENNReal.ofReal_mul (by linarith [hb.1] : 0 ≤ 2*b),
          ← ENNReal.ofReal_add (by linarith [ha.1]) (mul_nonneg (by linarith [hb.1]) hu')]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [add_one_le_exp (2*a+2*b*u)])
  refine (pow_le_pow_left' h' n).trans_eq ?_
  simp [eexp,← ENNReal.ofReal_pow (exp_pos _).le,← Real.exp_nat_mul]

end O71
