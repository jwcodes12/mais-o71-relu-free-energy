import Display

noncomputable section
open MeasureTheory Set Filter Real ProbabilityTheory
open scoped ENNReal Topology
namespace O71

abbrev inputLaw : Measure ℝ := ProbabilityTheory.cond volume (Icc (-1 : ℝ) 1)
instance : IsProbabilityMeasure inputLaw := by
  apply cond_isProbabilityMeasure_of_finite <;> norm_num [Real.volume_Icc]
abbrev noiseLaw := gaussianReal 0 1
abbrev obsLaw := inputLaw.prod noiseLaw
abbrev Sample (n : ℕ) := Fin n → ℝ × ℝ
abbrev sampleLaw (n : ℕ) : Measure (Sample n) := Measure.pi (fun _ => obsLaw)

def eexp (x : ℝ) := ENNReal.ofReal (exp x)
@[simp] theorem eexp_zero : eexp 0 = 1 := by simp [eexp]
theorem eexp_add (x y : ℝ) : eexp (x+y) = eexp x * eexp y := by
  simp [eexp,exp_add,ENNReal.ofReal_mul (exp_pos _).le]

def ratio (a y : ℝ) := eexp (a*y-a^2/2)

theorem gaussian_tilt (a b : ℝ) :
    ∫⁻ y, eexp (a*y+b) ∂noiseLaw = eexp (a^2/2+b) := by
  simp_rw [eexp_add]
  rw [lintegral_mul_const _ (by unfold eexp; fun_prop)]
  congr 1
  unfold eexp
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _) (by filter_upwards with x; positivity)]
  congr 1
  simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) a

theorem gaussian_pair (a b : ℝ) :
    ∫⁻ y, ratio a y * ratio b y ∂noiseLaw = eexp (a*b) := by
  simp only [ratio, ← eexp_add]
  calc
    _ = ∫⁻ y, eexp ((a+b)*y+(-(a^2+b^2)/2)) ∂noiseLaw := by
      apply lintegral_congr; intro y; congr 1; ring
    _ = _ := (gaussian_tilt ..).trans (by congr 1; ring)

def likelihood {n : ℕ} (f : ℝ → ℝ) (s : Sample n) :=
  ∏ i, ratio (f (s i).1) (s i).2

theorem likelihood_pair {n : ℕ} {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ s, likelihood f s * likelihood g s ∂sampleLaw n =
      (∫⁻ x, eexp (f x*g x) ∂inputLaw)^n := by
  let h := fun p : ℝ × ℝ => ratio (f p.1) p.2 * ratio (g p.1) p.2
  have hm : Measurable h := by unfold h ratio eexp; fun_prop
  have he : (∫⁻ p, h p ∂obsLaw) = ∫⁻ x, eexp (f x*g x) ∂inputLaw := by
    rw [lintegral_prod _ hm.aemeasurable]
    exact lintegral_congr fun x => gaussian_pair (f x) (g x)
  simp only [likelihood,← Finset.prod_mul_distrib]
  change (∫⁻ s, ∏ i, h (s i) ∂sampleLaw n) = _
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (s : Sample n) => h (s i)) (iIndepFun_pi fun _ => hm.aemeasurable)
    (fun i => hm.comp (measurable_pi_apply i))]
  have hev (i : Fin n) : (∫⁻ s : Sample n, h (s i) ∂sampleLaw n) = ∫⁻ p, h p ∂obsLaw :=
    (measurePreserving_eval (fun _ : Fin n => obsLaw) i).lintegral_comp hm
  simp_rw [hev, he]
  simp

theorem likelihood_mean {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    ∫⁻ s, likelihood f s ∂sampleLaw n = 1 := by
  simpa [likelihood,ratio] using likelihood_pair (n := n) hf (g := fun _ => 0) measurable_const

abbrev ballW := Metric.closedBall center (1/3)
abbrev prior := ProbabilityTheory.cond volume ballW
instance : IsProbabilityMeasure prior := cond_isProbabilityMeasure_of_finite
  (Metric.measure_closedBall_pos volume _ (by norm_num)).ne' (isCompact_closedBall _ _).measure_ne_top

def evidence {n : ℕ} (s : Sample n) := ∫⁻ w, likelihood (prediction w) s ∂prior
def excess {n : ℕ} (s : Sample n) := -log (evidence s).toReal

@[fun_prop] theorem prediction_measurable : Measurable (fun p : Space × ℝ => prediction p.1 p.2) := by
  unfold prediction; fun_prop

theorem evidence_mean (n : ℕ) : ∫⁻ s : Sample n, evidence s ∂sampleLaw n = 1 := by
  unfold evidence
  rw [lintegral_lintegral_swap]
  · have h (w : Space) : (∫⁻ s : Sample n, likelihood (prediction w) s ∂sampleLaw n) = 1 :=
      likelihood_mean (by unfold prediction; fun_prop)
    simp_rw [h]
    simp
  · unfold Function.uncurry likelihood ratio eexp prediction; fun_prop

#print axioms likelihood_pair
end O71
